use std::{collections::BTreeSet, path::Path};

use rustc_hir::ItemKind;
use rustc_middle::mir::{visit::Visitor, Location, Operand, Place, Rvalue};
use rustc_session::config::Input;

use crate::compile_util;

pub fn run_path(path: &Path) {
    analyze(compile_util::path_to_input(path));
}

pub fn run_code(code: &str) {
    analyze(compile_util::str_to_input(code));
}

fn analyze(input: Input) {
    let config = compile_util::make_config(input);
    compile_util::run_compiler(config, |source_map, tcx| {
        let hir = tcx.hir();
        for id in hir.items() {
            let item = hir.item(id);

            let params = if let ItemKind::Fn(sig, _, _) = &item.kind {
                sig.decl.inputs.len()
            } else {
                continue;
            };

            let file = compile_util::span_to_path(item.span, source_map);
            let name = item.ident.name.to_ident_string();

            let def_id = item.item_id().owner_id.def_id.to_def_id();
            let body = tcx.optimized_mir(def_id);

            let mut visitor = RwVisitor::new(params);
            visitor.visit_body(body);

            if !visitor.writes.is_empty() {
                println!("{:?}: {}", file, name);
                println!("reads: {:?}", visitor.reads);
                println!("writes: {:?}", visitor.writes);
            }

            // for (i, bbd) in body.basic_blocks.iter().enumerate() {
            //     println!("{}", i);
            //     for stmt in &bbd.statements {
            //         println!("{:?}", stmt.kind);
            //     }
            //     if let Some(term) = &bbd.terminator {
            //         println!("{:?}", term.kind);
            //     }
            // }
        }
    });
}

struct RwVisitor {
    params: usize,
    reads: BTreeSet<usize>,
    writes: BTreeSet<usize>,
}

impl RwVisitor {
    fn new(params: usize) -> Self {
        Self {
            params,
            reads: BTreeSet::new(),
            writes: BTreeSet::new(),
        }
    }
}

impl<'tcx> Visitor<'tcx> for RwVisitor {
    fn visit_assign(&mut self, place: &Place<'tcx>, rvalue: &Rvalue<'tcx>, location: Location) {
        if place.is_indirect() {
            let i = place.local.index();
            if i <= self.params {
                self.writes.insert(i);
            }
        }
        self.super_assign(place, rvalue, location);
    }

    fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
        if let Rvalue::Use(Operand::Copy(r) | Operand::Move(r)) | Rvalue::CopyForDeref(r) = rvalue {
            if r.is_indirect() {
                let i = r.local.index();
                if i <= self.params {
                    self.reads.insert(i);
                }
            }
        }
        self.super_rvalue(rvalue, location);
    }
}
