use std::collections::{BTreeMap, BTreeSet, VecDeque};

use rustc_abi::VariantIdx;
use rustc_middle::{
    mir::{Body, Local, Location, Terminator, TerminatorKind},
    ty::{Ty, TyCtxt, TyKind},
};

use super::domains::*;

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

pub fn analyze_code(code: &str) {
    let input = crate::compile_util::str_to_input(code);
    let config = crate::compile_util::make_config(input);
    crate::compile_util::run_compiler(config, |_, tcx| {
        let hir = tcx.hir();
        for id in hir.items() {
            let item = hir.item(id);
            let inputs = if let rustc_hir::ItemKind::Fn(sig, _, _) = &item.kind {
                sig.decl.inputs.len()
            } else {
                continue;
            };
            let def_id = item.item_id().owner_id.def_id.to_def_id();
            let body = tcx.optimized_mir(def_id);
            let mut analyzer = Analyzer {
                tcx,
                inputs,
                alloc_param_map: BTreeMap::new(),
                param_tys: vec![],
            };
            let result = analyzer.analyze_body(body);
            show_analysis_result(body, &result);
        }
    });
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

#[derive(Clone)]
pub struct Analyzer<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub inputs: usize,
    pub alloc_param_map: BTreeMap<usize, usize>,
    pub param_tys: Vec<TypeInfo>,
}

impl<'tcx> Analyzer<'tcx> {
    pub fn analyze_body(&mut self, body: &Body<'tcx>) -> BTreeMap<Label, AbsState> {
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
                let places = v.ptrv.gamma().unwrap();
                assert_eq!(places.len(), 1);
                let place = places.first().unwrap();
                let alloc = if let AbsBase::Heap(alloc) = place.base {
                    alloc
                } else {
                    unreachable!()
                };
                self.alloc_param_map.insert(alloc, i);
            }
            start_state.local.set(i, v);
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
            let (new_next_state, next_locations) = if statement_index < bbd.statements.len() {
                let stmt = &bbd.statements[statement_index];
                let new_next_state = self.transfer_statement(stmt, state);
                let next_location = Location {
                    block,
                    statement_index: statement_index + 1,
                };
                (new_next_state, vec![next_location])
            } else {
                let terminator = bbd.terminator.as_ref().unwrap();
                let new_next_state = self.transfer_terminator(terminator, state);
                let next_locations = next_locations_of_terminator(terminator);
                (new_next_state, next_locations)
            };
            for location in next_locations {
                let next_label = Label {
                    location,
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

        states
    }

    pub fn expands_path(&self, place: &AbsPath) -> Vec<AbsPath> {
        expands_path(&place.0, &self.param_tys, vec![])
            .into_iter()
            .map(AbsPath)
            .collect()
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

fn next_locations_of_terminator(terminator: &Terminator<'_>) -> Vec<Location> {
    match &terminator.kind {
        TerminatorKind::Goto { target } => vec![Location {
            block: *target,
            statement_index: 0,
        }],
        TerminatorKind::SwitchInt { targets, .. } => targets
            .all_targets()
            .iter()
            .map(|&target| Location {
                block: target,
                statement_index: 0,
            })
            .collect(),
        TerminatorKind::UnwindResume => vec![],
        TerminatorKind::UnwindTerminate(_) => vec![],
        TerminatorKind::Return => vec![],
        TerminatorKind::Unreachable => vec![],
        TerminatorKind::Drop { target, .. } => vec![Location {
            block: *target,
            statement_index: 0,
        }],
        TerminatorKind::Call { target, .. } => {
            if let Some(target) = target {
                vec![Location {
                    block: *target,
                    statement_index: 0,
                }]
            } else {
                vec![]
            }
        }
        TerminatorKind::Assert { target, .. } => vec![Location {
            block: *target,
            statement_index: 0,
        }],
        TerminatorKind::Yield { .. } => unreachable!("{:?}", terminator.kind),
        TerminatorKind::GeneratorDrop => unreachable!("{:?}", terminator.kind),
        TerminatorKind::FalseEdge { .. } => unreachable!("{:?}", terminator.kind),
        TerminatorKind::FalseUnwind { .. } => unreachable!("{:?}", terminator.kind),
        TerminatorKind::InlineAsm { .. } => unreachable!("{:?}", terminator.kind),
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
