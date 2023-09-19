use std::collections::{BTreeMap, VecDeque};

use rustc_middle::mir::{Body, Local, Location, Terminator, TerminatorKind};

use super::{domains::*, semantics};

#[derive(Default)]
struct WorkList(VecDeque<Location>);

impl WorkList {
    fn pop(&mut self) -> Option<Location> {
        self.0.pop_front()
    }

    fn push(&mut self, loc: Location) {
        self.0.push_back(loc)
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
            println!("{:?}", def_id);
            analyze_body(body, inputs);
        }
    });
}

pub fn analyze_body(body: &Body<'_>, inputs: usize) {
    let mut work_list = WorkList::default();
    let mut states: BTreeMap<Location, AbsState> = BTreeMap::new();

    let mut start_state = AbsState::bot(body.local_decls.len());
    for i in 1..=inputs {
        let ty = &body.local_decls[Local::from_usize(i)].ty;
        let v = semantics::top_value_of_ty(ty);
        start_state.local.set(i, v);
    }

    let start = Location::START;
    states.insert(start, start_state);
    work_list.push(start);

    let bot = AbsState::bot(body.local_decls.len());
    while let Some(location) = work_list.pop() {
        let state = states.get(&location).unwrap_or(&bot);
        let Location {
            block,
            statement_index,
        } = location;
        let bbd = &body.basic_blocks[block];
        let (new_next_state, next_locations) = if statement_index < bbd.statements.len() {
            let stmt = &bbd.statements[statement_index];
            let new_next_state = semantics::transfer_statement(stmt, state);
            let next_location = Location {
                block,
                statement_index: statement_index + 1,
            };
            (new_next_state, vec![next_location])
        } else {
            let terminator = bbd.terminator.as_ref().unwrap();
            let new_next_state = semantics::transfer_terminator(terminator, state);
            let next_locations = next_locations_of_terminator(terminator);
            (new_next_state, next_locations)
        };
        for next_location in next_locations {
            let next_state = states.get(&next_location).unwrap_or(&bot);
            let joined = next_state.join(&new_next_state);
            if !joined.ord(next_state) {
                states.insert(next_location, joined);
                work_list.push(next_location);
            }
        }
    }

    for block in body.basic_blocks.indices() {
        let bbd = &body.basic_blocks[block];
        println!("{:?}", block);
        for (statement_index, stmt) in bbd.statements.iter().enumerate() {
            let location = Location {
                block,
                statement_index,
            };
            let state = states.get(&location).unwrap_or(&bot);
            println!("{:?}", state);
            println!("{:?}", stmt);
        }
        if let Some(terminator) = bbd.terminator.as_ref() {
            let location = Location {
                block,
                statement_index: bbd.statements.len(),
            };
            let state = states.get(&location).unwrap_or(&bot);
            println!("{:?}", state);
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
