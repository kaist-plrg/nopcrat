use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    path::Path,
};

use rustc_abi::VariantIdx;
use rustc_middle::{
    hir::nested_filter,
    mir::{Body, ClearCrossCrate, Local, LocalInfo, Location, TerminatorKind},
    ty::{Ty, TyCtxt, TyKind},
};
use rustc_session::config::Input;
use rustc_span::def_id::DefId;

use super::domains::*;
use crate::*;

pub fn analyze_path(path: &Path) {
    analyze_input(compile_util::path_to_input(path));
}

pub fn analyze_code(code: &str) {
    analyze_input(compile_util::str_to_input(code));
}

pub fn analyze_input(input: Input) -> BTreeMap<DefId, FunctionSummary> {
    let config = compile_util::make_config(input);
    compile_util::run_compiler(config, |_, tcx| analyze(tcx)).unwrap()
}

pub fn analyze(tcx: TyCtxt<'_>) -> BTreeMap<DefId, FunctionSummary> {
    let hir = tcx.hir();

    let mut call_graph = BTreeMap::new();
    let mut inputs_map = BTreeMap::new();
    for id in hir.items() {
        let item = hir.item(id);
        let inputs = if let rustc_hir::ItemKind::Fn(sig, _, _) = &item.kind {
            sig.decl.inputs.len()
        } else {
            continue;
        };
        let def_id = item.item_id().owner_id.def_id.to_def_id();
        inputs_map.insert(def_id, inputs);
        let mut visitor = CallVisitor::new(tcx);
        use rustc_hir::intravisit::Visitor;
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

    let mut summaries = BTreeMap::new();
    for id in &po {
        let def_ids = elems.get(id).unwrap();
        assert_eq!(def_ids.len(), 1);

        let def_id = *def_ids.iter().next().unwrap();
        println!("{:?}", def_id);

        let static_tys = get_static_tys(def_id, tcx);
        let inputs = *inputs_map.get(&def_id).unwrap();
        let body = tcx.optimized_mir(def_id);
        let mut analyzer = Analyzer::new(tcx, inputs, static_tys, summaries);
        let (result, init_state) = analyzer.analyze_body(body);
        summaries = analyzer.summaries;
        show_analysis_result(body, &result);
        let return_states = return_location(body)
            .map(|ret| {
                result
                    .into_iter()
                    .filter_map(|(label, state)| {
                        if label.location == ret {
                            Some(state)
                        } else {
                            None
                        }
                    })
                    .collect()
            })
            .unwrap_or_default();
        let summary = FunctionSummary::new(init_state, return_states);
        summaries.insert(def_id, summary);
    }
    summaries
}

pub struct Analyzer<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub inputs: usize,
    pub static_tys: BTreeMap<DefId, Ty<'tcx>>,
    pub summaries: BTreeMap<DefId, FunctionSummary>,

    pub alloc_param_map: BTreeMap<usize, usize>,
    pub param_tys: Vec<TypeInfo>,
    pub static_allocs: BTreeMap<DefId, usize>,
}

impl<'tcx> Analyzer<'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        inputs: usize,
        static_tys: BTreeMap<DefId, Ty<'tcx>>,
        summaries: BTreeMap<DefId, FunctionSummary>,
    ) -> Self {
        Self {
            tcx,
            inputs,
            static_tys,
            summaries,
            alloc_param_map: BTreeMap::new(),
            param_tys: vec![],
            static_allocs: BTreeMap::new(),
        }
    }
}

impl<'tcx> Analyzer<'tcx> {
    pub fn analyze_body(&mut self, body: &Body<'tcx>) -> (BTreeMap<Label, AbsState>, AbsState) {
        for (i, local) in body.local_decls.iter().enumerate() {
            if i > self.inputs {
                break;
            }
            let ty = if let TyKind::RawPtr(tm) = local.ty.kind() {
                TypeInfo::from_ty(&tm.ty, self.tcx)
            } else {
                TypeInfo::NonStruct
            };
            self.param_tys.push(ty);
        }

        let mut work_list = WorkList::default();
        let mut states: BTreeMap<Label, AbsState> = BTreeMap::new();

        let mut start_state = AbsState::bot(body.local_decls.len());
        start_state.writes = MustPathSet::top();

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

        let start_label = Label {
            location: Location::START,
            writes: start_state.writes.clone(),
            reads: start_state.reads.clone(),
        };
        states.insert(start_label.clone(), start_state);
        work_list.push(start_label.clone());

        let bot = AbsState::bot(body.local_decls.len());
        while let Some(label) = work_list.pop() {
            let state = states.get(&label).unwrap_or(&bot);
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
                let (new_next_states, next_locations) = self.transfer_terminator(terminator, state);
                (new_next_states, next_locations)
            };
            for new_next_state in new_next_states {
                for location in &next_locations {
                    let next_label = Label {
                        location: *location,
                        writes: new_next_state.writes.clone(),
                        reads: new_next_state.reads.clone(),
                    };
                    let next_state = states.get(&next_label).unwrap_or(&bot);
                    let joined = next_state.join(&new_next_state);
                    if !joined.ord(next_state) {
                        states.insert(next_label.clone(), joined);
                        work_list.push(next_label);
                    }
                }
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

impl<'tcx> rustc_hir::intravisit::Visitor<'tcx> for CallVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.tcx.hir()
    }

    fn visit_expr(&mut self, expr: &'tcx rustc_hir::Expr<'tcx>) {
        use rustc_hir::{def, ExprKind};
        if let ExprKind::Call(callee, _) = expr.kind {
            if let ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) = callee.kind {
                if let def::Res::Def(def::DefKind::Fn, def_id) = path.res {
                    self.callees.insert(def_id);
                }
            }
        }
        rustc_hir::intravisit::walk_expr(self, expr);
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Label {
    pub location: Location,
    pub writes: MustPathSet,
    pub reads: MayPathSet,
}

#[derive(Default)]
struct WorkList(VecDeque<Label>);

impl WorkList {
    fn pop(&mut self) -> Option<Label> {
        self.0.pop_front()
    }

    fn push(&mut self, label: Label) {
        self.0.push_back(label)
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

#[allow(unused)]
fn show_analysis_result(body: &Body<'_>, states: &BTreeMap<Label, AbsState>) {
    for block in body.basic_blocks.indices() {
        let bbd = &body.basic_blocks[block];
        println!("{:?}", block);
        for (statement_index, stmt) in bbd.statements.iter().enumerate() {
            let location = Location {
                block,
                statement_index,
            };
            for (label, state) in states {
                if label.location != location {
                    continue;
                }
                println!("{:?}", state);
            }
            println!("{:?}", stmt);
        }
        if let Some(terminator) = bbd.terminator.as_ref() {
            let location = Location {
                block,
                statement_index: bbd.statements.len(),
            };
            for (label, state) in states {
                if label.location != location {
                    continue;
                }
                println!("{:?}", state);
            }
            println!("{:?}", terminator);
        }
    }
}

pub fn get_static_tys(def_id: DefId, tcx: TyCtxt<'_>) -> BTreeMap<DefId, Ty<'_>> {
    let body = tcx.mir_built(def_id.as_local().unwrap()).borrow();
    let mut static_tys = BTreeMap::new();
    for local in &body.local_decls {
        if let ClearCrossCrate::Set(box LocalInfo::StaticRef { def_id, .. }) = &local.local_info {
            static_tys.insert(*def_id, local.ty);
        }
    }
    static_tys
}

pub fn return_location(body: &Body<'_>) -> Option<Location> {
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
