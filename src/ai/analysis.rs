use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
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
        visit::Visitor as MVisitor, Body, ClearCrossCrate, Constant, ConstantKind, Local,
        LocalInfo, Location, TerminatorKind,
    },
    ty::{Ty, TyCtxt, TyKind},
};
use rustc_session::config::Input;
use rustc_span::def_id::DefId;

use super::domains::*;
use crate::{rustc_data_structures::graph::WithSuccessors as _, *};

pub fn analyze_path(path: &Path) {
    analyze_input(compile_util::path_to_input(path));
}

pub fn analyze_code(code: &str) {
    analyze_input(compile_util::str_to_input(code));
}

pub fn analyze_input(input: Input) {
    let config = compile_util::make_config(input);
    compile_util::run_compiler(config, |_, tcx| {
        let results = analyze(tcx);
        for (def_id, (summary, param_tys)) in results {
            let reads: BTreeSet<_> = summary
                .return_states
                .iter()
                .flat_map(|st| st.rw.reads.as_set())
                .map(|p| p.base())
                .collect();
            if summary.return_states.iter().any(|st| st.rw.writes.is_bot()) {
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
                    let writes = st.rw.writes.as_set();
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
            println!("{}:", tcx.def_path_str(def_id));
            for w in writes {
                let must = ret_writes.iter().all(|(_, writes)| writes.contains(&w));
                println!("  {:?}{}", w, if must { " (must)" } else { " (may)" });
                if !must {
                    let (wst, nwst): (Vec<_>, Vec<_>) = ret_writes
                        .iter()
                        .partition(|(_, writes)| writes.contains(&w));
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
                    println!("  {:?} / {:?}", w, nw);
                }
            }
        }
    });
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

    let static_tys_map: BTreeMap<_, _> = funcs
        .iter()
        .map(|def_id| (*def_id, get_static_tys(*def_id, tcx)))
        .collect();

    let mut param_tys_map = BTreeMap::new();
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
                    let len = tcx.optimized_mir(*def_id).local_decls.len();
                    let _ = input_summaries.try_insert(*def_id, FunctionSummary::bot(len));
                }
            }

            for def_id in def_ids {
                println!("{:?}", def_id);
                tracing::info!("{:?}", def_id);
                let inputs = *inputs_map.get(def_id).unwrap();
                let static_tys = static_tys_map.get(def_id).unwrap().clone();
                let body = tcx.optimized_mir(def_id);
                let param_tys = get_param_tys(body, inputs, tcx);
                let alloc_ty_map = get_alloc_ty_map(body, tcx);
                let loop_heads = get_loop_heads(body);

                param_tys_map
                    .entry(*def_id)
                    .or_insert_with(|| param_tys.clone());

                let mut analyzer = Analyzer::new(
                    tcx,
                    inputs,
                    param_tys,
                    static_tys,
                    alloc_ty_map,
                    loop_heads,
                    input_summaries.clone(),
                );
                let summary = analyzer.make_summary(body);

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
        .map(|(def_id, summary)| (def_id, (summary, param_tys_map.remove(&def_id).unwrap())))
        .collect()
}

pub struct Analyzer<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub inputs: usize,
    pub param_tys: Vec<TypeInfo>,
    pub static_tys: BTreeMap<DefId, Ty<'tcx>>,
    pub literal_ty_map: BTreeMap<AllocId, Ty<'tcx>>,
    pub loop_heads: BTreeSet<Location>,
    pub summaries: BTreeMap<DefId, FunctionSummary>,

    pub alloc_param_map: BTreeMap<usize, usize>,
    pub static_allocs: BTreeMap<DefId, usize>,
    pub literal_allocs: BTreeMap<AllocId, usize>,
    pub label_alloc_map: BTreeMap<Label, usize>,
    pub label_user_fn_alloc_map: BTreeMap<(Label, RwSets), BTreeMap<usize, usize>>,
}

impl<'tcx> Analyzer<'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        inputs: usize,
        param_tys: Vec<TypeInfo>,
        static_tys: BTreeMap<DefId, Ty<'tcx>>,
        literal_ty_map: BTreeMap<AllocId, Ty<'tcx>>,
        loop_heads: BTreeSet<Location>,
        summaries: BTreeMap<DefId, FunctionSummary>,
    ) -> Self {
        Self {
            tcx,
            inputs,
            param_tys,
            static_tys,
            literal_ty_map,
            loop_heads,
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
    ) -> (BTreeMap<Location, BTreeMap<RwSets, AbsState>>, AbsState) {
        let mut work_list: WorkList;
        let mut states: BTreeMap<Location, BTreeMap<RwSets, AbsState>>;

        let mut start_state = AbsState::bot(body.local_decls.len());
        start_state.rw.writes = MustPathSet::top();

        for i in 1..=self.inputs {
            let ty = &body.local_decls[Local::from_usize(i)].ty;
            let v = self.top_value_of_ty(ty, Some(&mut start_state.heap), &mut BTreeSet::new());
            if matches!(ty.kind(), TyKind::RawPtr(_)) {
                self.alloc_param_map.insert(v.heap_addr(), i);
            }
            start_state.local.set(i, v);
        }

        let init_state = start_state.clone();

        for (def_id, ty) in &self.static_tys {
            let v = self.top_value_of_ty(ty, Some(&mut start_state.heap), &mut BTreeSet::new());
            self.static_allocs.insert(*def_id, v.heap_addr());
        }

        for (alloc_id, ty) in &self.literal_ty_map {
            let v = self.top_value_of_ty(ty, Some(&mut start_state.heap), &mut BTreeSet::new());
            let i = start_state.heap.push(v);
            self.literal_allocs.insert(*alloc_id, i);
        }

        let start_label = Label {
            location: Location::START,
            rw: start_state.rw.clone(),
        };
        let bot = AbsState::bot(body.local_decls.len());

        loop {
            work_list = WorkList::default();
            work_list.push(start_label.clone());

            states = BTreeMap::new();
            states
                .entry(start_label.location)
                .or_default()
                .insert(start_label.rw.clone(), start_state.clone());

            let mut restart = false;
            while let Some(label) = work_list.pop() {
                let state = states
                    .get(&label.location)
                    .and_then(|states| states.get(&label.rw))
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
                for new_next_state in new_next_states {
                    for location in &next_locations {
                        let next_state = states
                            .get(location)
                            .and_then(|states| states.get(&new_next_state.rw))
                            .unwrap_or(&bot);
                        let joined = next_state.join(&new_next_state);
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
                                rw: new_next_state.rw.clone(),
                            };
                            states
                                .entry(*location)
                                .or_default()
                                .insert(next_label.rw.clone(), joined);
                            work_list.push(next_label);
                        }
                    }
                }
                for next_location in next_locations {
                    if !self.loop_heads.contains(&next_location) {
                        continue;
                    }
                    let len = states.get(&next_location).unwrap().keys().len();
                    if len > 10 {
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
        expands_path(&place.0, &self.param_tys, vec![])
            .into_iter()
            .map(AbsPath)
            .collect()
    }

    pub fn def_id_to_string(&self, def_id: DefId) -> String {
        self.tcx.def_path(def_id).to_string_no_crate_verbose()
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

    fn bot(len: usize) -> Self {
        Self {
            init_state: AbsState::bot(len),
            return_states: vec![],
        }
    }

    fn return_state_map(&self) -> BTreeMap<&RwSets, &AbsState> {
        self.return_states.iter().map(|s| (&s.rw, s)).collect()
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
    pub rw: RwSets,
}

#[derive(Default, Debug)]
struct WorkList(VecDeque<Label>);

impl WorkList {
    fn pop(&mut self) -> Option<Label> {
        self.0.pop_front()
    }

    fn push(&mut self, label: Label) {
        if !self.0.contains(&label) {
            self.0.push_back(label)
        }
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
    states: &BTreeMap<Location, BTreeMap<RwSets, AbsState>>,
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
        if let TypeInfo::Struct(fields) = &tys[*first] {
            expands_path(&path[1..], fields, curr)
        } else {
            vec![curr]
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
