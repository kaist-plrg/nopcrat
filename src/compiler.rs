use std::path::Path;

use rustc_hir::{FnRetTy, ItemKind};

use crate::compile_util;

pub fn run(path: &Path) {
    let input = compile_util::path_to_input(path);
    let config = compile_util::make_config(input);
    compile_util::run_compiler(config, |source_map, tcx| {
        let hir = tcx.hir();
        for id in hir.items() {
            let item = hir.item(id);
            if let ItemKind::Fn(sig, _, _) = &item.kind {
                let name = item.ident.name.to_ident_string();
                let file = compile_util::span_to_path(item.span, source_map).unwrap();
                let mut tys: Vec<_> = sig.decl.inputs.iter().collect();
                if let FnRetTy::Return(ty) = &sig.decl.output {
                    tys.push(ty);
                }
                if tys
                    .into_iter()
                    .any(|ty| source_map.span_to_snippet(ty.span).unwrap() == "*mut libc::c_void")
                {
                    println!("{:?} {}", file, name);
                }
            }
        }
    });
}
