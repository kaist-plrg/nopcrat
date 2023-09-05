use std::{
    collections::BTreeMap,
    fs::File,
    io::{Read, Write},
    path::Path,
};

use rustc_hir::{ForeignItemKind, ItemKind};

use crate::compile_util;

pub fn run(path: &Path) {
    let input = compile_util::path_to_input(path);
    let config = compile_util::make_config(input);
    let suggestions: Vec<_> = compile_util::run_compiler(config, |compiler| {
        compiler.enter(|queries| {
            queries.global_ctxt().unwrap().enter(|tcx| {
                let source_map = compiler.session().source_map();
                let hir = tcx.hir();

                let mut functions = BTreeMap::new();
                let mut foreigns: BTreeMap<_, Vec<_>> = BTreeMap::new();
                let mut foreign_spans: BTreeMap<_, _> = BTreeMap::new();
                let mut dir = path.to_path_buf();
                dir.pop();

                for id in hir.items() {
                    let item = hir.item(id);
                    if matches!(item.kind, ItemKind::Fn(_, _, _)) {
                        if let Some(p) = compile_util::span_to_path(item.span, source_map) {
                            let name = item.ident.name.to_ident_string();
                            let mut p = p.strip_prefix(&dir).unwrap().to_path_buf();
                            p.set_extension("");
                            let rp: String = std::iter::once("crate")
                                .chain(p.components().map(|c| c.as_os_str().to_str().unwrap()))
                                .chain(std::iter::once(name.as_str()))
                                .intersperse("::")
                                .collect();
                            functions.insert(name, rp);
                        }
                    }
                    if let rustc_hir::ItemKind::ForeignMod { items, .. } = &item.kind {
                        if let Some(p) = compile_util::span_to_path(item.span, source_map) {
                            foreign_spans.insert(p.clone(), item.span);
                            for item in items.iter() {
                                let item = hir.foreign_item(item.id);
                                if matches!(item.kind, ForeignItemKind::Fn(_, _, _)) {
                                    let name = item.ident.name.to_ident_string();
                                    foreigns
                                        .entry(p.clone())
                                        .or_default()
                                        .push((name, item.span));
                                }
                            }
                        }
                    }
                }

                foreigns
                    .into_iter()
                    .filter_map(|(p, fs)| {
                        let (rps, spans): (Vec<_>, Vec<_>) = fs
                            .into_iter()
                            .filter_map(|(f, span)| functions.get(&f).map(|rp| (rp, span)))
                            .unzip();
                        let fspan = foreign_spans.get(&p).unwrap().shrink_to_lo();
                        let suggestions: Vec<_> = rps
                            .into_iter()
                            .map(|rp| {
                                let stmt = format!("use {};\n", rp);
                                let snippet = compile_util::span_to_snippet(fspan, source_map);
                                compile_util::make_suggestion(snippet, &stmt)
                            })
                            .chain(spans.into_iter().map(|span| {
                                let snippet = compile_util::span_to_snippet(span, source_map);
                                compile_util::make_suggestion(snippet, "")
                            }))
                            .collect();
                        if suggestions.is_empty() {
                            None
                        } else {
                            Some((p, suggestions))
                        }
                    })
                    .collect()
            })
        })
    })
    .unwrap();

    for (p, suggestions) in suggestions {
        let mut file = File::open(&p).unwrap();
        let mut contents = String::new();
        file.read_to_string(&mut contents).unwrap();
        let fixed = rustfix::apply_suggestions(&contents, &suggestions).unwrap();

        let mut file = File::create(&p).unwrap();
        file.write_all(fixed.as_bytes()).unwrap();
    }
}
