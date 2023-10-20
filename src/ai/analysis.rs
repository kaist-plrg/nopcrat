use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::Write as _,
    path::Path,
};

use rustc_abi::VariantIdx;
use rustc_const_eval::interpret::{AllocId, ConstValue, GlobalAlloc, Scalar};
use rustc_hir::{
    def::{DefKind, Res},
    intravisit::Visitor as HVisitor,
    Expr, ExprKind, QPath,
};
use rustc_middle::{
    hir::nested_filter,
    mir::{
        visit::Visitor as MVisitor, BasicBlock, Body, ClearCrossCrate, Constant, ConstantKind,
        Local, LocalInfo, Location, TerminatorKind,
    },
    ty::{Ty, TyCtxt, TyKind},
};
use rustc_session::config::Input;
use rustc_span::{def_id::DefId, Span};
use serde::{Deserialize, Serialize};

use super::domains::*;
use crate::{rustc_data_structures::graph::WithSuccessors as _, *};

pub fn analyze_path(path: &Path) -> BTreeMap<String, Vec<OutputParam>> {
    analyze_input(compile_util::path_to_input(path))
}

pub fn analyze_code(code: &str) -> BTreeMap<String, Vec<OutputParam>> {
    analyze_input(compile_util::str_to_input(code))
}

pub fn analyze_input(input: Input) -> BTreeMap<String, Vec<OutputParam>> {
    let config = compile_util::make_config(input);
    compile_util::run_compiler(config, |tcx| {
        let results = analyze(tcx);
        collect_output_params(results, tcx)
    })
    .unwrap()
}

pub fn collect_output_params(
    results: BTreeMap<DefId, (FunctionSummary, Vec<TypeInfo>)>,
    tcx: TyCtxt<'_>,
) -> BTreeMap<String, Vec<OutputParam>> {
    let mut func_param_map = BTreeMap::new();
    for (def_id, (summary, param_tys)) in results {
        let reads: BTreeSet<_> = summary
            .return_states
            .iter()
            .flat_map(|st| st.reads.as_set())
            .map(|p| p.base())
            .collect();
        if summary.return_states.iter().any(|st| st.writes.is_bot()) {
            continue;
        }
        let expanded_map: BTreeMap<_, BTreeSet<_>> = (1..param_tys.len())
            .map(|i| {
                let expanded = expands_path(&[i], &param_tys, vec![]).into_iter().collect();
                (i, expanded)
            })
            .collect();
        let ret_writes: Vec<_> = summary
            .return_states
            .iter()
            .map(|st| {
                let writes = st.writes.as_set();
                let mut per_base: BTreeMap<_, BTreeSet<_>> = BTreeMap::new();
                for w in writes {
                    per_base.entry(w.base()).or_default().insert(w.0.clone());
                }
                let writes: BTreeSet<_> = per_base
                    .into_iter()
                    .filter_map(|(i, paths)| {
                        if reads.contains(&i) || expanded_map.get(&i).unwrap() != &paths {
                            None
                        } else {
                            Some(i)
                        }
                    })
                    .collect();
                (st.local.get(0).clone(), writes)
            })
            .collect();
        let writes: BTreeSet<_> = ret_writes
            .iter()
            .flat_map(|(_, writes)| writes)
            .cloned()
            .collect();
        if writes.is_empty() {
            continue;
        }
        let body = tcx.optimized_mir(def_id);
        let ret_ty = &body.local_decls[Local::from_usize(0)].ty;
        let params = writes
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
                    index,
                    must,
                    return_values,
                }
            })
            .collect();
        func_param_map.insert(tcx.def_path_str(def_id), params);
    }
    func_param_map
}

pub fn analyze(tcx: TyCtxt<'_>) -> BTreeMap<DefId, (FunctionSummary, Vec<TypeInfo>)> {
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

    let mut info_map: BTreeMap<_, _> = funcs
        .iter()
        .map(|def_id| {
            let inputs = *inputs_map.get(def_id).unwrap();
            let static_tys = get_static_tys(*def_id, tcx);
            let body = tcx.optimized_mir(def_id);
            let param_tys = get_param_tys(body, inputs, tcx);
            let literal_ty_map = get_alloc_ty_map(body, tcx);
            let dominating_map = get_dominating_map(body);
            let loop_heads = get_loop_heads(body);
            let rpo_map = get_rpo_map(body);
            let info = FuncInfo {
                inputs,
                static_tys,
                param_tys,
                literal_ty_map,
                dominating_map,
                loop_heads,
                rpo_map,
            };
            (*def_id, info)
        })
        .collect();

    let mut summaries = BTreeMap::new();
    for id in &po {
        let def_ids = elems.get(id).unwrap();
        let recursive = if def_ids.len() == 1 {
            let def_id = def_ids.first().unwrap();
            call_graph.get(def_id).unwrap().contains(def_id)
        } else {
            true
        };

        loop {
            let mut input_summaries = summaries.clone();
            if recursive {
                for def_id in def_ids {
                    let _ = input_summaries.try_insert(*def_id, FunctionSummary::bot());
                }
            }

            for def_id in def_ids {
                println!("{:?}", def_id);
                tracing::info!("{:?}", def_id);
                let mut analyzer =
                    Analyzer::new(tcx, info_map.get(def_id).unwrap(), input_summaries.clone());
                let summary = analyzer.make_summary(tcx.optimized_mir(*def_id));

                let summary = if let Some(old) = input_summaries.get(def_id) {
                    summary.join(old)
                } else {
                    summary
                };
                summaries.insert(*def_id, summary);
            }

            if !recursive
                || def_ids.iter().all(|def_id| {
                    let old = input_summaries.get(def_id).unwrap();
                    let new = summaries.get(def_id).unwrap();
                    new.ord(old)
                })
            {
                break;
            }
        }
    }

    summaries
        .into_iter()
        .map(|(def_id, summary)| {
            (
                def_id,
                (summary, info_map.remove(&def_id).unwrap().param_tys),
            )
        })
        .collect()
}

#[derive(Debug, Serialize, Deserialize)]
pub struct OutputParam {
    pub index: usize,
    pub must: bool,
    pub return_values: ReturnValues,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ReturnValues {
    None,
    Int(AbsInt, AbsInt),
    Uint(AbsUint, AbsUint),
    Bool(AbsBool, AbsBool),
}

#[derive(Debug, Clone)]
struct FuncInfo<'tcx> {
    inputs: usize,
    param_tys: Vec<TypeInfo>,
    static_tys: BTreeMap<DefId, Ty<'tcx>>,
    literal_ty_map: BTreeMap<AllocId, Ty<'tcx>>,
    dominating_map: BTreeMap<BasicBlock, BTreeSet<BasicBlock>>,
    loop_heads: BTreeSet<Location>,
    rpo_map: BTreeMap<BasicBlock, usize>,
}

pub struct Analyzer<'a, 'tcx> {
    pub tcx: TyCtxt<'tcx>,
    info: &'a FuncInfo<'tcx>,
    pub summaries: BTreeMap<DefId, FunctionSummary>,

    pub alloc_param_map: BTreeMap<usize, usize>,
    pub static_allocs: BTreeMap<DefId, usize>,
    pub literal_allocs: BTreeMap<AllocId, usize>,
    pub label_alloc_map: BTreeMap<Label, usize>,
    pub label_user_fn_alloc_map: BTreeMap<(Label, MustPathSet), BTreeMap<usize, usize>>,
}

impl<'a, 'tcx> Analyzer<'a, 'tcx> {
    fn new(
        tcx: TyCtxt<'tcx>,
        info: &'a FuncInfo<'tcx>,
        summaries: BTreeMap<DefId, FunctionSummary>,
    ) -> Self {
        Self {
            tcx,
            info,
            summaries,
            alloc_param_map: BTreeMap::new(),
            static_allocs: BTreeMap::new(),
            literal_allocs: BTreeMap::new(),
            label_alloc_map: BTreeMap::new(),
            label_user_fn_alloc_map: BTreeMap::new(),
        }
    }

    fn make_summary(&mut self, body: &Body<'tcx>) -> FunctionSummary {
        let (mut result, init_state) = self.analyze_body(body);
        tracing::info!("\n{}", analysis_result_to_string(body, &result).unwrap());

        let return_states = return_location(body)
            .and_then(|ret| result.remove(&ret))
            .map(|states| states.into_values().collect())
            .unwrap_or_default();
        FunctionSummary::new(init_state, return_states)
    }

    pub fn analyze_body(
        &mut self,
        body: &Body<'tcx>,
    ) -> (
        BTreeMap<Location, BTreeMap<MustPathSet, AbsState>>,
        AbsState,
    ) {
        let mut work_list: WorkList<'_>;
        let mut states: BTreeMap<Location, BTreeMap<MustPathSet, AbsState>>;

        let mut start_state = AbsState::bot();
        start_state.writes = MustPathSet::top();

        for i in 1..=self.info.inputs {
            let ty = &body.local_decls[Local::from_usize(i)].ty;
            let v = self.top_value_of_ty(ty, Some(&mut start_state.heap), &mut BTreeSet::new());
            if matches!(ty.kind(), TyKind::RawPtr(_)) {
                self.alloc_param_map.insert(v.heap_addr(), i);
            }
            start_state.local.set(i, v);
        }

        let init_state = start_state.clone();

        for (def_id, ty) in &self.info.static_tys {
            let v = self.top_value_of_ty(ty, Some(&mut start_state.heap), &mut BTreeSet::new());
            self.static_allocs.insert(*def_id, v.heap_addr());
        }

        for (alloc_id, ty) in &self.info.literal_ty_map {
            let v = self.top_value_of_ty(ty, Some(&mut start_state.heap), &mut BTreeSet::new());
            let i = start_state.heap.push(v);
            self.literal_allocs.insert(*alloc_id, i);
        }

        let start_label = Label {
            location: Location::START,
            writes: start_state.writes.clone(),
        };
        let bot = AbsState::bot();

        let mut merging_blocks: BTreeSet<BasicBlock> = BTreeSet::new();
        loop {
            work_list = WorkList::new(&self.info.rpo_map);
            work_list.push(start_label.clone());

            states = BTreeMap::new();
            states
                .entry(start_label.location)
                .or_default()
                .insert(start_label.writes.clone(), start_state.clone());

            let mut restart = false;
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
                    let terminator = bbd.terminator.as_ref().unwrap();
                    let (new_next_states, next_locations) =
                        self.transfer_terminator(terminator, state, &label);
                    (new_next_states, next_locations)
                };
                for location in &next_locations {
                    if merging_blocks.contains(&location.block) {
                        let next_state = if let Some(states) = states.get(location) {
                            assert_eq!(states.len(), 1);
                            states.first_key_value().unwrap().1
                        } else {
                            &bot
                        };
                        let mut joined = next_state.clone();
                        for new_next_state in &new_next_states {
                            joined = joined.join(new_next_state);
                        }
                        if !joined.ord(next_state) {
                            let max = joined
                                .local
                                .iter()
                                .chain(joined.heap.iter())
                                .flat_map(|v| v.allocs())
                                .max();
                            if let Some(max) = max {
                                assert!(max < joined.heap.len(), "{:?}", joined);
                            }

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
                            let joined = next_state.join(new_next_state);
                            if !joined.ord(next_state) {
                                let max = joined
                                    .local
                                    .iter()
                                    .chain(joined.heap.iter())
                                    .flat_map(|v| v.allocs())
                                    .max();
                                if let Some(max) = max {
                                    assert!(max < joined.heap.len(), "{:?}", joined);
                                }
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
                for next_location in next_locations {
                    if !self.info.loop_heads.contains(&next_location) {
                        continue;
                    }
                    let len = states.get(&next_location).unwrap().keys().len();
                    if len > 3 {
                        merging_blocks
                            .extend(self.info.dominating_map.get(&next_location.block).unwrap());
                        restart = true;
                    }
                }
                if restart {
                    break;
                }
            }
            if !restart {
                break;
            }
        }

        (states, init_state)
    }

    pub fn expands_path(&self, place: &AbsPath) -> Vec<AbsPath> {
        expands_path(&place.0, &self.info.param_tys, vec![])
            .into_iter()
            .map(AbsPath)
            .collect()
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
    pub return_states: Vec<AbsState>,
}

impl FunctionSummary {
    fn new(init_state: AbsState, return_states: Vec<AbsState>) -> Self {
        Self {
            init_state,
            return_states,
        }
    }

    fn bot() -> Self {
        Self {
            init_state: AbsState::bot(),
            return_states: vec![],
        }
    }

    fn return_state_map(&self) -> BTreeMap<&MustPathSet, &AbsState> {
        self.return_states.iter().map(|s| (&s.writes, s)).collect()
    }

    fn join(&self, that: &Self) -> Self {
        let init_state = self.init_state.join(&that.init_state);
        let this_map = self.return_state_map();
        let that_map = that.return_state_map();
        let keys: BTreeSet<_> = this_map.keys().chain(that_map.keys()).collect();
        let return_states = keys
            .into_iter()
            .map(|k| match (this_map.get(k), that_map.get(k)) {
                (Some(v1), Some(v2)) => v1.join(v2),
                (Some(v), None) | (None, Some(v)) => (*v).clone(),
                _ => unreachable!(),
            })
            .collect();
        Self::new(init_state, return_states)
    }

    fn ord(&self, that: &Self) -> bool {
        self.init_state.ord(&that.init_state) && {
            let this_map = self.return_state_map();
            let that_map = that.return_state_map();
            this_map
                .iter()
                .all(|(k, v)| that_map.get(k).map_or(false, |w| v.ord(w)))
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

struct LiteralVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    alloc_ty_map: BTreeMap<AllocId, Ty<'tcx>>,
}

impl<'tcx> LiteralVisitor<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            alloc_ty_map: BTreeMap::new(),
        }
    }
}

impl<'tcx> MVisitor<'tcx> for LiteralVisitor<'tcx> {
    fn visit_constant(&mut self, constant: &Constant<'tcx>, location: Location) {
        if let ConstantKind::Val(ConstValue::Scalar(Scalar::Ptr(ptr, _)), ty) = constant.literal {
            if matches!(
                self.tcx.global_alloc(ptr.provenance),
                GlobalAlloc::Memory(_)
            ) {
                if let TyKind::Ref(_, ty, _) = ty.kind() {
                    if ty.is_array() {
                        self.alloc_ty_map.insert(ptr.provenance, *ty);
                    }
                }
            }
        }
        self.super_constant(constant, location);
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
        let block_idx = self.rpo_map.get(&label.location.block).unwrap();
        let labels = self
            .labels
            .entry((*block_idx, label.location.statement_index))
            .or_default();
        if !labels.contains(&label) {
            labels.push(label)
        }
    }

    fn remove_location(&mut self, location: Location) {
        let block_idx = self.rpo_map.get(&location.block).unwrap();
        self.labels.remove(&(*block_idx, location.statement_index));
    }

    #[allow(unused)]
    fn len(&self) -> usize {
        self.labels.values().map(|v| v.len()).sum()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum TypeInfo {
    Struct(Vec<TypeInfo>),
    NonStruct,
}

impl TypeInfo {
    fn from_ty<'tcx>(ty: &Ty<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        if let TyKind::Adt(adt_def, generic_args) = ty.kind() {
            if adt_def.is_struct() {
                let variant = adt_def.variant(VariantIdx::from_usize(0));
                return Self::Struct(
                    variant
                        .fields
                        .iter()
                        .map(|field| Self::from_ty(&field.ty(tcx, generic_args), tcx))
                        .collect(),
                );
            }
        }
        Self::NonStruct
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

fn get_static_tys(def_id: DefId, tcx: TyCtxt<'_>) -> BTreeMap<DefId, Ty<'_>> {
    let body = tcx.mir_built(def_id.as_local().unwrap()).borrow();
    let mut static_tys = BTreeMap::new();
    for local in &body.local_decls {
        if let ClearCrossCrate::Set(box LocalInfo::StaticRef { def_id, .. }) = &local.local_info {
            static_tys.insert(*def_id, local.ty);
        }
    }
    static_tys
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

fn get_alloc_ty_map<'tcx>(body: &Body<'tcx>, tcx: TyCtxt<'tcx>) -> BTreeMap<AllocId, Ty<'tcx>> {
    let mut visitor = LiteralVisitor::new(tcx);
    visitor.visit_body(body);
    visitor.alloc_ty_map
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

fn get_dominating_map(body: &Body<'_>) -> BTreeMap<BasicBlock, BTreeSet<BasicBlock>> {
    let dominators = body.basic_blocks.dominators();
    let map = body
        .basic_blocks
        .indices()
        .map(|bb| (bb, dominators.dominators(bb).collect()))
        .collect();
    graph::inverse(&map)
}

fn get_loop_heads(body: &Body<'_>) -> BTreeSet<Location> {
    let dominators = body.basic_blocks.dominators();
    body.basic_blocks
        .indices()
        .flat_map(|bb| {
            let mut doms: Vec<_> = dominators.dominators(bb).collect();
            let succs: BTreeSet<_> = body.basic_blocks.successors(bb).collect();
            doms.retain(|dom| succs.contains(dom));
            doms
        })
        .map(|bb| bb.start_location())
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
