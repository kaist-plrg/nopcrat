use std::path::Path;

use rustc_middle::mir::Body;
use rustc_session::config::Input;

use crate::compile_util;

pub fn size_path(path: &Path) {
    size_input(compile_util::path_to_input(path))
}

pub fn size_code(code: &str) {
    size_input(compile_util::str_to_input(code))
}

fn size_input(input: Input) {
    let config = compile_util::make_config(input);
    compile_util::run_compiler(config, |tcx| {
        let mut funcs: usize = 0;
        let mut blocks: usize = 0;
        let mut stmts: usize = 0;

        for id in tcx.hir_free_items() {
            let item = tcx.hir_item(id);
            if item.ident.name.to_ident_string() == "main" {
                continue;
            }
            if !matches!(item.kind, rustc_hir::ItemKind::Fn { .. }) {
                continue;
            }

            let def_id = id.owner_id.to_def_id();
            let body = tcx.optimized_mir(def_id);
            funcs += 1;
            blocks += body.basic_blocks.len();
            stmts += body_size(body);
        }

        println!("{} {} {}", funcs, blocks, stmts);
    })
    .unwrap()
}

fn body_size(body: &Body<'_>) -> usize {
    body.basic_blocks
        .iter()
        .map(|bbd| bbd.statements.len() + bbd.terminator.is_some() as usize)
        .sum()
}
