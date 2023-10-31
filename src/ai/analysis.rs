use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::Write as _,
    path::Path,
};

use rustc_abi::VariantIdx;
use rustc_hir::{
    def::{DefKind, Res},
    intravisit::Visitor as HVisitor,
    Expr, ExprKind, HirId, QPath,
};
use rustc_index::bit_set::BitSet;
use rustc_middle::{
    hir::nested_filter,
    mir::{BasicBlock, Body, Local, Location, ProjectionElem, StatementKind, TerminatorKind},
    ty::{AdtKind, Ty, TyCtxt, TyKind, TypeAndMut},
};
use rustc_session::config::Input;
use rustc_span::{def_id::DefId, Span};
use serde::{Deserialize, Serialize};

use super::domains::*;
use crate::{
    rustc_data_structures::graph::WithSuccessors as _, rustc_mir_dataflow::Analysis as _, *,
};

#[derive(Debug, Clone, Copy)]
pub struct AnalysisConfig {
    pub max_loop_head_states: usize,
    pub widening: bool,
    pub verbose: bool,
}

impl Default for AnalysisConfig {
    fn default() -> Self {
        Self {
            max_loop_head_states: 1,
            widening: true,
            verbose: false,
        }
    }
}

pub type AnalysisResult = BTreeMap<String, Vec<OutputParam>>;

pub fn analyze_path(path: &Path, conf: &AnalysisConfig) -> AnalysisResult {
    analyze_input(compile_util::path_to_input(path), conf)
}

pub fn analyze_code(code: &str, conf: &AnalysisConfig) -> AnalysisResult {
    analyze_input(compile_util::str_to_input(code), conf)
}

pub fn analyze_input(input: Input, conf: &AnalysisConfig) -> AnalysisResult {
    let config = compile_util::make_config(input);
    compile_util::run_compiler(config, |tcx| {
        analyze(tcx, conf)
            .into_iter()
            .filter_map(|(def_id, (_, params))| {
                if params.is_empty() {
                    None
                } else {
                    Some((tcx.def_path_str(def_id), params))
                }
            })
            .collect()
    })
    .unwrap()
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Write {
    All,
    Partial,
    None,
}

pub fn analyze(
    tcx: TyCtxt<'_>,
    conf: &AnalysisConfig,
) -> BTreeMap<DefId, (FunctionSummary, Vec<OutputParam>)> {
    let hir = tcx.hir();

    let mut call_graph = BTreeMap::new();
    let mut inputs_map = BTreeMap::new();
    for id in hir.items() {
        let item = hir.item(id);
        if item.ident.name.to_ident_string() == "main" {
            continue;
        }
        let inputs = if let rustc_hir::ItemKind::Fn(sig, _, _) = &item.kind {
            sig.decl.inputs.len()
        } else {
            continue;
        };
        let def_id = item.item_id().owner_id.def_id.to_def_id();
        inputs_map.insert(def_id, inputs);
        let mut visitor = CallVisitor::new(tcx);
        visitor.visit_item(item);
        call_graph.insert(def_id, visitor.callees);
    }

    let funcs: BTreeSet<_> = call_graph.keys().cloned().collect();
    for callees in call_graph.values_mut() {
        callees.retain(|callee| funcs.contains(callee));
    }
    let (graph, elems) = graph::compute_sccs(&call_graph);
    let inv_graph = graph::inverse(&graph);
    let po: Vec<_> = graph::post_order(&graph, &inv_graph)
        .into_iter()
        .flatten()
        .collect();

    let mut visitor = FnPtrVisitor::new(tcx);
    tcx.hir().visit_all_item_likes_in_crate(&mut visitor);

    let info_map: BTreeMap<_, _> = funcs
        .iter()
        .map(|def_id| {
            let inputs = inputs_map[def_id];
            let body = tcx.optimized_mir(def_id);
            let param_tys = get_param_tys(body, inputs, tcx);
            let pre_rpo_map = get_rpo_map(body);
            let loop_blocks = get_loop_blocks(body, &pre_rpo_map);
            let rpo_map = compute_rpo_map(body, &loop_blocks);
            let dead_locals = get_dead_locals(body, tcx);
            let fn_ptr = visitor.fn_ptrs.contains(def_id);
            let info = FuncInfo {
                inputs,
                param_tys,
                loop_blocks,
                rpo_map,
                dead_locals,
                fn_ptr,
            };
            (*def_id, info)
        })
        .collect();

    let mut ptr_params_map = BTreeMap::new();
    let mut output_params_map = BTreeMap::new();
    let mut summaries = BTreeMap::new();
    let mut results = BTreeMap::new();
    for id in &po {
        let def_ids = &elems[id];
        let recursive = if def_ids.len() == 1 {
            let def_id = def_ids.first().unwrap();
            call_graph[def_id].contains(def_id)
        } else {
            true
        };

        loop {
            if recursive {
                for def_id in def_ids {
                    let _ = summaries.try_insert(*def_id, FunctionSummary::bot());
                }
            }

            let mut need_rerun = false;
            for def_id in def_ids {
                tracing::info!("{:?}", def_id);
                let mut analyzer = Analyzer::new(tcx, &info_map[def_id], conf, &summaries);
                let body = tcx.optimized_mir(*def_id);
                if conf.verbose {
                    println!(
                        "{:?} {} {}",
                        def_id,
                        body.basic_blocks.len(),
                        body.local_decls.len()
                    );
                }

                let (result, init_state) = analyzer.analyze_body(body);
                tracing::info!("\n{}", analysis_result_to_string(body, &result).unwrap());

                let return_states = return_location(body)
                    .and_then(|ret| result.get(&ret))
                    .cloned()
                    .unwrap_or_default();
                let summary = FunctionSummary::new(init_state, return_states);
                results.insert(*def_id, result);
                ptr_params_map.insert(*def_id, analyzer.ptr_params);

                let (summary, updated) = if let Some(old) = summaries.get(def_id) {
                    let new_summary = summary.join(old);
                    let updated = !new_summary.ord(old);
                    (new_summary, updated)
                } else {
                    (summary, false)
                };
                summaries.insert(*def_id, summary);
                need_rerun |= updated;
            }

            if !need_rerun {
                for def_id in def_ids {
                    let mut analyzer = Analyzer::new(tcx, &info_map[def_id], conf, &summaries);
                    analyzer.ptr_params = ptr_params_map.remove(def_id).unwrap();
                    let summary = &summaries[def_id];
                    let return_ptrs = analyzer.get_return_ptrs(summary);
                    let mut output_params =
                        analyzer.find_output_params(summary, &return_ptrs, *def_id);
                    let result = results.remove(def_id).unwrap();
                    for p in &mut output_params {
                        analyzer.find_complete_write(p, &result, *def_id);
                    }
                    output_params_map.insert(*def_id, output_params);
                }
                break;
            }
        }
    }

    summaries
        .into_iter()
        .map(|(def_id, summary)| {
            let output_params = output_params_map.remove(&def_id).unwrap();
            (def_id, (summary, output_params))
        })
        .collect()
}

#[derive(Debug, Serialize, Deserialize)]
pub struct OutputParam {
    pub index: usize,
    pub must: bool,
    pub return_values: ReturnValues,
    pub complete_writes: Vec<(usize, usize)>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ReturnValues {
    None,
    Int(AbsInt, AbsInt),
    Uint(AbsUint, AbsUint),
    Bool(AbsBool, AbsBool),
}

#[derive(Debug, Clone)]
struct FuncInfo {
    inputs: usize,
    param_tys: Vec<TypeInfo>,
    loop_blocks: BTreeMap<BasicBlock, BTreeSet<BasicBlock>>,
    rpo_map: BTreeMap<BasicBlock, usize>,
    dead_locals: Vec<BitSet<Local>>,
    fn_ptr: bool,
}

impl FuncInfo {
    fn expands_path(&self, place: &AbsPath) -> Vec<AbsPath> {
        expands_path(&place.0, &self.param_tys, vec![])
            .into_iter()
            .map(AbsPath)
            .collect()
    }
}

pub struct Analyzer<'a, 'tcx> {
    pub tcx: TyCtxt<'tcx>,
    info: &'a FuncInfo,
    conf: &'a AnalysisConfig,
    pub summaries: &'a BTreeMap<DefId, FunctionSummary>,
    pub ptr_params: Vec<usize>,
}

impl<'a, 'tcx> Analyzer<'a, 'tcx> {
    fn new(
        tcx: TyCtxt<'tcx>,
        info: &'a FuncInfo,
        conf: &'a AnalysisConfig,
        summaries: &'a BTreeMap<DefId, FunctionSummary>,
    ) -> Self {
        Self {
            tcx,
            info,
            conf,
            summaries,
            ptr_params: vec![],
        }
    }

    fn get_return_ptrs(&self, summary: &FunctionSummary) -> BTreeSet<usize> {
        summary
            .return_states
            .values()
            .flat_map(|st| {
                let v = st.local.get(0);
                self.get_read_paths_of_ptr(&v.ptrv, &[])
            })
            .map(|p| p.base())
            .collect()
    }

    fn find_output_params(
        &self,
        summary: &FunctionSummary,
        return_ptrs: &BTreeSet<usize>,
        def_id: DefId,
    ) -> Vec<OutputParam> {
        if self.info.fn_ptr {
            return vec![];
        }
        let reads: BTreeSet<_> = summary
            .return_states
            .values()
            .flat_map(|st| st.reads.as_set())
            .map(|p| p.base())
            .collect();
        if summary.return_states.values().any(|st| st.writes.is_bot()) {
            return vec![];
        }
        let expanded_map: BTreeMap<_, BTreeSet<_>> = (1..=self.info.inputs)
            .map(|i| {
                let expanded = self
                    .expands_path(&AbsPath(vec![i]))
                    .into_iter()
                    .map(|p| p.0)
                    .collect();
                (i, expanded)
            })
            .collect();
        let writes: Vec<BTreeMap<_, _>> = summary
            .return_states
            .values()
            .map(|st| {
                let writes = st.writes.as_set();
                let mut per_base: BTreeMap<_, BTreeSet<_>> = BTreeMap::new();
                for w in writes {
                    per_base.entry(w.base()).or_default().insert(w.0.clone());
                }
                expanded_map
                    .iter()
                    .map(|(i, paths)| {
                        let w = if let Some(ws) = per_base.get(i) {
                            if ws == paths {
                                Write::All
                            } else {
                                Write::Partial
                            }
                        } else {
                            Write::None
                        };
                        (*i, w)
                    })
                    .collect()
            })
            .collect();
        let writes: BTreeSet<_> = (1..=self.info.inputs)
            .filter(|i| {
                let ws: BTreeSet<_> = writes.iter().map(|map| map[&i]).collect();
                !reads.contains(i)
                    && !return_ptrs.contains(i)
                    && self.info.param_tys[*i] != TypeInfo::Union
                    && ws.contains(&Write::All)
                    && !ws.contains(&Write::Partial)
            })
            .collect();
        if writes.is_empty() {
            return vec![];
        }
        let ret_writes: Vec<_> = summary
            .return_states
            .values()
            .map(|st| {
                let mut writes2: BTreeSet<_> =
                    st.writes.as_set().iter().map(|w| w.base()).collect();
                writes2.retain(|w| writes.contains(w));
                (st.local.get(0).clone(), writes2)
            })
            .collect();
        let body = self.tcx.optimized_mir(def_id);
        let ret_ty = &body.local_decls[Local::from_usize(0)].ty;
        writes
            .into_iter()
            .map(|index| {
                let must = ret_writes.iter().all(|(_, writes)| writes.contains(&index));
                let return_values = if !must {
                    let (wst, nwst): (Vec<_>, Vec<_>) = ret_writes
                        .iter()
                        .partition(|(_, writes)| writes.contains(&index));
                    let w = wst
                        .into_iter()
                        .map(|(v, _)| v)
                        .cloned()
                        .reduce(|a, b| a.join(&b))
                        .unwrap();
                    let nw = nwst
                        .into_iter()
                        .map(|(v, _)| v)
                        .cloned()
                        .reduce(|a, b| a.join(&b))
                        .unwrap();
                    match ret_ty.kind() {
                        TyKind::Int(_) => ReturnValues::Int(w.intv.clone(), nw.intv.clone()),
                        TyKind::Uint(_) => ReturnValues::Uint(w.uintv.clone(), nw.uintv.clone()),
                        TyKind::Bool => ReturnValues::Bool(w.boolv, nw.boolv),
                        _ => ReturnValues::None,
                    }
                } else {
                    ReturnValues::None
                };
                OutputParam {
                    index: index - 1,
                    must,
                    return_values,
                    complete_writes: vec![],
                }
            })
            .collect()
    }

    fn find_complete_write(
        &self,
        param: &mut OutputParam,
        result: &BTreeMap<Location, BTreeMap<MustPathSet, AbsState>>,
        def_id: DefId,
    ) {
        if param.must {
            return;
        }

        let paths = self.expands_path(&AbsPath(vec![param.index + 1]));
        if paths[0].0.len() == 1 {
            return;
        }

        let body = self.tcx.optimized_mir(def_id);
        for (location, sts) in result {
            let complete = sts.keys().any(|w| {
                let w = w.as_set();
                paths.iter().all(|p| w.contains(p))
            });
            if !complete {
                continue;
            }
            if location.statement_index == 0 {
                continue;
            }
            let mut prev = *location;
            prev.statement_index -= 1;
            let pcomplete = result[&prev].keys().any(|w| {
                let w = w.as_set();
                paths.iter().all(|p| w.contains(p))
            });
            if !pcomplete {
                let Location {
                    block,
                    statement_index,
                } = prev;
                let bbd = &body.basic_blocks[block];
                let stmt = &bbd.statements[statement_index];
                let StatementKind::Assign(box (p, _)) = stmt.kind else {
                    continue;
                };
                if p.projection
                    .iter()
                    .any(|proj| matches!(proj, ProjectionElem::Field(_, _)))
                {
                    param
                        .complete_writes
                        .push((block.as_usize(), statement_index));
                }
            }
        }
    }

    pub fn analyze_body(
        &mut self,
        body: &Body<'tcx>,
    ) -> (
        BTreeMap<Location, BTreeMap<MustPathSet, AbsState>>,
        AbsState,
    ) {
        let mut start_state = AbsState::bot();
        start_state.writes = MustPathSet::top();

        for i in 1..=self.info.inputs {
            let ty = &body.local_decls[Local::from_usize(i)].ty;
            let v = if let TyKind::RawPtr(TypeAndMut { ty, .. }) = ty.kind() {
                let v = self.top_value_of_ty(ty);
                let idx = start_state.args.push(v);
                self.ptr_params.push(i);
                AbsValue::arg(idx)
            } else {
                self.top_value_of_ty(ty)
            };
            start_state.local.set(i, v);
        }

        let init_state = start_state.clone();

        let start_label = Label {
            location: Location::START,
            writes: start_state.writes.clone(),
        };
        let bot = AbsState::bot();

        let loop_heads: BTreeSet<Location> = self
            .info
            .loop_blocks
            .keys()
            .map(|bb| bb.start_location())
            .collect();
        let mut merging_blocks = if self.conf.max_loop_head_states <= 1 {
            self.info.loop_blocks.values().flatten().cloned().collect()
        } else {
            BTreeSet::new()
        };

        let states = 'analysis_loop: loop {
            let mut work_list = WorkList::new(&self.info.rpo_map);
            work_list.push(start_label.clone());

            let mut states: BTreeMap<_, BTreeMap<_, _>> = BTreeMap::new();
            states
                .entry(start_label.location)
                .or_default()
                .insert(start_label.writes.clone(), start_state.clone());

            while let Some(label) = work_list.pop() {
                let state = states
                    .get(&label.location)
                    .and_then(|states| states.get(&label.writes))
                    .unwrap_or(&bot);
                tracing::info!("\n{:?}\n{:?}", label, state);
                let Location {
                    block,
                    statement_index,
                } = label.location;
                let bbd = &body.basic_blocks[block];
                let (new_next_states, next_locations) = if statement_index < bbd.statements.len() {
                    let stmt = &bbd.statements[statement_index];
                    let new_next_state = self.transfer_statement(stmt, state);
                    let next_location = Location {
                        block,
                        statement_index: statement_index + 1,
                    };
                    (vec![new_next_state], vec![next_location])
                } else {
                    let (new_next_states, next_locations) =
                        self.transfer_terminator(bbd.terminator(), state);
                    (new_next_states, next_locations)
                };
                for location in &next_locations {
                    let dead_locals = &self.info.dead_locals[location.block.as_usize()];
                    if merging_blocks.contains(&location.block) {
                        let next_state = if let Some(states) = states.get(location) {
                            assert_eq!(states.len(), 1);
                            states.first_key_value().unwrap().1
                        } else {
                            &bot
                        };
                        let mut joined = next_state.clone();
                        if let Some(st) = new_next_states.first() {
                            let mut new_next_state = st.clone();
                            for st in new_next_states.iter().skip(1) {
                                new_next_state = new_next_state.join(st);
                            }
                            if loop_heads.contains(location) && self.conf.widening {
                                joined = joined.widen(&new_next_state);
                            } else {
                                joined = joined.join(&new_next_state);
                            }
                        }
                        if location.statement_index == 0 {
                            joined.local.clear_dead_locals(dead_locals);
                        }
                        if !joined.ord(next_state) {
                            work_list.remove_location(*location);
                            let next_label = Label {
                                location: *location,
                                writes: joined.writes.clone(),
                            };
                            work_list.push(next_label);

                            let mut new_map = BTreeMap::new();
                            new_map.insert(joined.writes.clone(), joined);
                            states.insert(*location, new_map);
                        }
                    } else {
                        for new_next_state in &new_next_states {
                            let next_state = states
                                .get(location)
                                .and_then(|states| states.get(&new_next_state.writes))
                                .unwrap_or(&bot);
                            let mut joined = if loop_heads.contains(location) && self.conf.widening
                            {
                                next_state.widen(new_next_state)
                            } else {
                                next_state.join(new_next_state)
                            };
                            if location.statement_index == 0 {
                                joined.local.clear_dead_locals(dead_locals);
                            }
                            if !joined.ord(next_state) {
                                let next_label = Label {
                                    location: *location,
                                    writes: new_next_state.writes.clone(),
                                };
                                states
                                    .entry(*location)
                                    .or_default()
                                    .insert(next_label.writes.clone(), joined);
                                work_list.push(next_label);
                            }
                        }
                    }
                }
                let mut restart = false;
                for next_location in next_locations {
                    for blocks in self.info.loop_blocks.values() {
                        if !blocks.contains(&next_location.block) {
                            continue;
                        }
                        let len = states[&next_location].keys().len();
                        if len > self.conf.max_loop_head_states {
                            merging_blocks.extend(blocks);
                            restart = true;
                        }
                    }
                }
                if restart {
                    continue 'analysis_loop;
                }
            }
            break states;
        };

        (states, init_state)
    }

    pub fn expands_path(&self, place: &AbsPath) -> Vec<AbsPath> {
        self.info.expands_path(place)
    }

    pub fn def_id_to_string(&self, def_id: DefId) -> String {
        self.tcx.def_path(def_id).to_string_no_crate_verbose()
    }

    pub fn span_to_string(&self, span: Span) -> String {
        self.tcx.sess.source_map().span_to_snippet(span).unwrap()
    }
}

#[derive(Clone, Debug)]
pub struct FunctionSummary {
    pub init_state: AbsState,
    pub return_states: BTreeMap<MustPathSet, AbsState>,
}

impl FunctionSummary {
    fn new(init_state: AbsState, return_states: BTreeMap<MustPathSet, AbsState>) -> Self {
        Self {
            init_state,
            return_states,
        }
    }

    fn bot() -> Self {
        Self {
            init_state: AbsState::bot(),
            return_states: BTreeMap::new(),
        }
    }

    fn join(&self, other: &Self) -> Self {
        let init_state = self.init_state.join(&other.init_state);
        let keys: BTreeSet<_> = self
            .return_states
            .keys()
            .chain(other.return_states.keys())
            .cloned()
            .collect();
        let return_states = keys
            .into_iter()
            .map(|k| {
                let v = match (self.return_states.get(&k), other.return_states.get(&k)) {
                    (Some(v1), Some(v2)) => v1.join(v2),
                    (Some(v), None) | (None, Some(v)) => (*v).clone(),
                    _ => unreachable!(),
                };
                (k, v)
            })
            .collect();
        Self::new(init_state, return_states)
    }

    fn ord(&self, other: &Self) -> bool {
        self.init_state.ord(&other.init_state) && {
            self.return_states
                .iter()
                .all(|(k, v)| other.return_states.get(k).map_or(false, |w| v.ord(w)))
        }
    }
}

struct CallVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    callees: BTreeSet<DefId>,
}

impl<'tcx> CallVisitor<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            callees: BTreeSet::new(),
        }
    }
}

impl<'tcx> HVisitor<'tcx> for CallVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.tcx.hir()
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        if let ExprKind::Call(callee, _) = expr.kind {
            if let ExprKind::Path(QPath::Resolved(_, path)) = callee.kind {
                if let Res::Def(DefKind::Fn, def_id) = path.res {
                    self.callees.insert(def_id);
                }
            }
        }
        rustc_hir::intravisit::walk_expr(self, expr);
    }
}

struct FnPtrVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    callees: BTreeSet<HirId>,
    fn_ptrs: BTreeSet<DefId>,
}

impl<'tcx> FnPtrVisitor<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            callees: BTreeSet::new(),
            fn_ptrs: BTreeSet::new(),
        }
    }
}

impl<'tcx> HVisitor<'tcx> for FnPtrVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.tcx.hir()
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        match expr.kind {
            ExprKind::Call(callee, _) => {
                self.callees.insert(callee.hir_id);
            }
            ExprKind::Path(QPath::Resolved(_, path)) => {
                if !self.callees.contains(&expr.hir_id) {
                    if let Res::Def(def_kind, def_id) = path.res {
                        if def_kind.is_fn_like() {
                            self.fn_ptrs.insert(def_id);
                        }
                    }
                }
            }
            _ => {}
        }
        rustc_hir::intravisit::walk_expr(self, expr);
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Label {
    pub location: Location,
    pub writes: MustPathSet,
}

#[derive(Debug)]
struct WorkList<'a> {
    rpo_map: &'a BTreeMap<BasicBlock, usize>,
    labels: BTreeMap<(usize, usize), Vec<Label>>,
}

impl<'a> WorkList<'a> {
    fn new(rpo_map: &'a BTreeMap<BasicBlock, usize>) -> Self {
        Self {
            rpo_map,
            labels: BTreeMap::new(),
        }
    }

    fn pop(&mut self) -> Option<Label> {
        let mut entry = self.labels.first_entry()?;
        let labels = entry.get_mut();
        let label = labels.pop().unwrap();
        if labels.is_empty() {
            entry.remove();
        }
        Some(label)
    }

    fn push(&mut self, label: Label) {
        let block_idx = self.rpo_map[&label.location.block];
        let labels = self
            .labels
            .entry((block_idx, label.location.statement_index))
            .or_default();
        if !labels.contains(&label) {
            labels.push(label)
        }
    }

    fn remove_location(&mut self, location: Location) {
        let block_idx = self.rpo_map[&location.block];
        self.labels.remove(&(block_idx, location.statement_index));
    }

    #[allow(unused)]
    fn len(&self) -> usize {
        self.labels.values().map(|v| v.len()).sum()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum TypeInfo {
    Struct(Vec<TypeInfo>),
    Union,
    NonStruct,
}

impl TypeInfo {
    fn from_ty<'tcx>(ty: &Ty<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        if let TyKind::Adt(adt_def, generic_args) = ty.kind() {
            match adt_def.adt_kind() {
                AdtKind::Struct => {
                    let variant = adt_def.variant(VariantIdx::from_usize(0));
                    let tys = variant
                        .fields
                        .iter()
                        .map(|field| Self::from_ty(&field.ty(tcx, generic_args), tcx))
                        .collect();
                    Self::Struct(tys)
                }
                AdtKind::Union => Self::Union,
                AdtKind::Enum => Self::NonStruct,
            }
        } else {
            Self::NonStruct
        }
    }
}

fn analysis_result_to_string(
    body: &Body<'_>,
    states: &BTreeMap<Location, BTreeMap<MustPathSet, AbsState>>,
) -> Result<String, Box<dyn std::error::Error>> {
    let mut res = String::new();
    for block in body.basic_blocks.indices() {
        let bbd = &body.basic_blocks[block];
        writeln!(&mut res, "block {:?}", block)?;
        for (statement_index, stmt) in bbd.statements.iter().enumerate() {
            let location = Location {
                block,
                statement_index,
            };
            if let Some(states) = states.get(&location) {
                for state in states.values() {
                    writeln!(&mut res, "{:?}", state)?;
                }
            }
            writeln!(&mut res, "{:?}", stmt)?;
        }
        if let Some(terminator) = bbd.terminator.as_ref() {
            let location = Location {
                block,
                statement_index: bbd.statements.len(),
            };
            if let Some(states) = states.get(&location) {
                for state in states.values() {
                    writeln!(&mut res, "{:?}", state)?;
                }
            }
            writeln!(&mut res, "{:?}", terminator)?;
        }
    }
    Ok(res)
}

fn get_param_tys<'tcx>(body: &Body<'tcx>, inputs: usize, tcx: TyCtxt<'tcx>) -> Vec<TypeInfo> {
    let mut param_tys = vec![];
    for (i, local) in body.local_decls.iter().enumerate() {
        if i > inputs {
            break;
        }
        let ty = if let TyKind::RawPtr(tm) = local.ty.kind() {
            TypeInfo::from_ty(&tm.ty, tcx)
        } else {
            TypeInfo::NonStruct
        };
        param_tys.push(ty);
    }
    param_tys
}

fn return_location(body: &Body<'_>) -> Option<Location> {
    for block in body.basic_blocks.indices() {
        let bbd = &body.basic_blocks[block];
        if let Some(terminator) = &bbd.terminator {
            if terminator.kind == TerminatorKind::Return {
                let location = Location {
                    block,
                    statement_index: bbd.statements.len(),
                };
                return Some(location);
            }
        }
    }
    None
}

fn get_rpo_map(body: &Body<'_>) -> BTreeMap<BasicBlock, usize> {
    body.basic_blocks
        .reverse_postorder()
        .iter()
        .enumerate()
        .map(|(i, bb)| (*bb, i))
        .collect()
}

fn get_loop_blocks(
    body: &Body<'_>,
    rpo_map: &BTreeMap<BasicBlock, usize>,
) -> BTreeMap<BasicBlock, BTreeSet<BasicBlock>> {
    let dominators = body.basic_blocks.dominators();
    let loop_heads: BTreeSet<_> = body
        .basic_blocks
        .indices()
        .flat_map(|bb| {
            let mut doms: Vec<_> = dominators.dominators(bb).collect();
            let succs: BTreeSet<_> = body.basic_blocks.successors(bb).collect();
            doms.retain(|dom| succs.contains(dom));
            doms
        })
        .collect();
    let mut loop_heads: Vec<_> = loop_heads.into_iter().collect();
    loop_heads.sort_by_key(|bb| rpo_map[bb]);

    let succ_map: BTreeMap<_, BTreeSet<_>> = body
        .basic_blocks
        .indices()
        .map(|bb| (bb, body.basic_blocks.successors(bb).collect()))
        .collect();
    let mut inv_map = graph::inverse(&succ_map);
    loop_heads
        .into_iter()
        .map(|head| {
            let reachables = graph::reachable_vertices(&inv_map, head);
            for succs in inv_map.values_mut() {
                succs.remove(&head);
            }
            let loop_blocks = body
                .basic_blocks
                .indices()
                .filter(|bb| dominators.dominates(head, *bb) && reachables.contains(bb))
                .collect();
            (head, loop_blocks)
        })
        .collect()
}

fn compute_rpo_map(
    body: &Body<'_>,
    loop_blocks: &BTreeMap<BasicBlock, BTreeSet<BasicBlock>>,
) -> BTreeMap<BasicBlock, usize> {
    fn traverse(
        current: BasicBlock,
        visited: &mut BTreeSet<BasicBlock>,
        po: &mut Vec<BasicBlock>,
        body: &Body<'_>,
        loop_blocks: &BTreeMap<BasicBlock, BTreeSet<BasicBlock>>,
    ) {
        if visited.contains(&current) {
            return;
        }
        visited.insert(current);
        let loops: Vec<_> = loop_blocks
            .values()
            .filter(|blocks| blocks.contains(&current))
            .collect();
        let mut succs: Vec<_> = body.basic_blocks.successors(current).collect();
        succs.sort_by_key(|succ| loops.iter().filter(|blocks| blocks.contains(succ)).count());
        for succ in succs {
            traverse(succ, visited, po, body, loop_blocks);
        }
        po.push(current);
    }
    let mut visited = BTreeSet::new();
    let mut rpo = vec![];
    traverse(
        BasicBlock::from_usize(0),
        &mut visited,
        &mut rpo,
        body,
        loop_blocks,
    );
    rpo.reverse();
    rpo.into_iter().enumerate().map(|(i, bb)| (bb, i)).collect()
}

fn get_dead_locals<'tcx>(body: &Body<'tcx>, tcx: TyCtxt<'tcx>) -> Vec<BitSet<Local>> {
    let mut borrowed_locals = rustc_mir_dataflow::impls::borrowed_locals(body);
    borrowed_locals.insert(Local::from_usize(0));
    let mut cursor = rustc_mir_dataflow::impls::MaybeLiveLocals
        .into_engine(tcx, body)
        .iterate_to_fixpoint()
        .into_results_cursor(body);
    body.basic_blocks
        .indices()
        .map(|bb| {
            cursor.seek_to_block_start(bb);
            let live_locals = cursor.get();
            let mut borrowed_or_live_locals = borrowed_locals.clone();
            borrowed_or_live_locals.union(live_locals);
            let mut dead_locals = BitSet::new_filled(body.local_decls.len());
            dead_locals.subtract(&borrowed_or_live_locals);
            dead_locals
        })
        .collect()
}

fn expands_path(path: &[usize], tys: &[TypeInfo], mut curr: Vec<usize>) -> Vec<Vec<usize>> {
    if let Some(first) = path.first() {
        curr.push(*first);
        if let Some(ty) = tys.get(*first) {
            if let TypeInfo::Struct(fields) = ty {
                expands_path(&path[1..], fields, curr)
            } else {
                vec![curr]
            }
        } else {
            tracing::warn!("unknown field access");
            vec![]
        }
    } else {
        tys.iter()
            .enumerate()
            .flat_map(|(n, ty)| {
                let mut curr = curr.clone();
                curr.push(n);
                if let TypeInfo::Struct(fields) = ty {
                    expands_path(path, fields, curr)
                } else {
                    vec![curr]
                }
            })
            .collect()
    }
}

#[allow(unused)]
fn body_size(body: &Body<'_>) -> usize {
    body.basic_blocks
        .iter()
        .map(|bbd| bbd.statements.len() + bbd.terminator.is_some() as usize)
        .sum()
}

#[allow(unused)]
fn show_body(body: &Body<'_>, stmt: bool, term: bool) {
    for bb in body.basic_blocks.indices() {
        println!("{:?}", bb);
        let bbd = &body.basic_blocks[bb];
        if stmt {
            for stmt in &bbd.statements {
                println!("{:?}", stmt);
            }
        }
        if term {
            if let Some(term) = &bbd.terminator {
                println!("{:?}", term.kind);
            }
        }
    }
}
