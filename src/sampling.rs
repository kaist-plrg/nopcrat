use std::path::Path;

use rustc_ast::Mutability;
use rustc_const_eval::interpret::ConstValue;
use rustc_middle::{
    mir::{visit::Visitor, Body, ConstantKind},
    ty::{TyCtxt, TyKind, TypeAndMut},
};
use rustc_session::config::Input;

use crate::{ai::analysis::AnalysisResult, compile_util};

pub fn sample_from_path(path: &Path, res: &AnalysisResult) -> Vec<String> {
    sample_from_input(compile_util::path_to_input(path), res)
}

pub fn sample_from_code(code: &str, res: &AnalysisResult) -> Vec<String> {
    sample_from_input(compile_util::str_to_input(code), res)
}

fn sample_from_input(input: Input, res: &AnalysisResult) -> Vec<String> {
    let config = compile_util::make_config(input);
    compile_util::run_compiler(config, |tcx| {
        let hir = tcx.hir();
        let mut fns = vec![];
        for id in hir.items() {
            let item = hir.item(id);
            if item.ident.name.to_ident_string() == "main" {
                continue;
            }
            if !matches!(item.kind, rustc_hir::ItemKind::Fn(_, _, _)) {
                continue;
            }
            let def_id = id.owner_id.to_def_id();
            let body = tcx.optimized_mir(def_id);
            let name = tcx.def_path_str(def_id);
            if !res.contains_key(&name)
                && body
                    .args_iter()
                    .any(|arg| match body.local_decls[arg].ty.kind() {
                        TyKind::RawPtr(TypeAndMut {
                            ty,
                            mutbl: Mutability::Mut,
                        }) => !ty.is_primitive() && !ty.is_c_void(tcx) && !ty.is_any_ptr(),
                        _ => false,
                    })
            // && has_call(body, tcx)
            {
                fns.push(name);
            }
        }
        fns
    })
    .unwrap()
}

#[allow(unused)]
fn has_call<'tcx>(body: &Body<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    let mut visitor = CallVisitor { tcx, b: false };
    visitor.visit_body(body);
    visitor.b
}

struct CallVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    b: bool,
}

impl<'tcx> Visitor<'tcx> for CallVisitor<'tcx> {
    fn visit_terminator(
        &mut self,
        terminator: &rustc_middle::mir::Terminator<'tcx>,
        location: rustc_middle::mir::Location,
    ) {
        if let rustc_middle::mir::TerminatorKind::Call { func, .. } = &terminator.kind {
            if let Some(constant) = func.constant() {
                if let ConstantKind::Val(ConstValue::ZeroSized, ty) = constant.literal {
                    if let TyKind::FnDef(def_id, _) = ty.kind() {
                        let name = self.tcx.def_path(*def_id).to_string_no_crate_verbose();
                        if name.contains("{extern#")
                            && (name.contains("cpy")
                                || name.contains("set")
                                || name.contains("move"))
                        {
                            self.b = true;
                        }
                    }
                }
            }
        }
        self.super_terminator(terminator, location);
    }
}
