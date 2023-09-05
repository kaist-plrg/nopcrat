use std::{
    collections::BTreeMap,
    fs::File,
    io::{Read, Write},
    path::Path,
};

use etrace::some_or;
use rustc_hir::{ForeignItemKind, ItemKind, QPath, TyKind};

use crate::compile_util;

pub fn run(path: &Path) {
    let input = compile_util::path_to_input(path);
    let config = compile_util::make_config(input);
    let suggestions = compile_util::run_compiler(config, |compiler| {
        compiler.enter(|queries| {
            queries.global_ctxt().unwrap().enter(|tcx| {
                let source_map = compiler.session().source_map();
                let hir = tcx.hir();

                let mut functions = BTreeMap::new();
                let mut foreigns: BTreeMap<_, Vec<_>> = BTreeMap::new();
                let mut fspans = BTreeMap::new();
                let mut types: BTreeMap<_, Vec<_>> = BTreeMap::new();
                let mut impls = BTreeMap::new();
                let mut dir = path.to_path_buf();
                dir.pop();

                for id in hir.items() {
                    let item = hir.item(id);
                    let name = item.ident.name.to_ident_string();
                    let p = some_or!(compile_util::span_to_path(item.span, source_map), continue);
                    match &item.kind {
                        ItemKind::Fn(_, _, _) => {
                            let rp = mk_rust_path(&dir, &p, &name);
                            functions.insert(name, rp);
                        }
                        ItemKind::ForeignMod { items, .. } => {
                            let _ = fspans.try_insert(p.clone(), item.span.shrink_to_lo());
                            let v = foreigns.entry(p).or_default();
                            for item in items.iter() {
                                let item = hir.foreign_item(item.id);
                                if !matches!(item.kind, ForeignItemKind::Fn(_, _, _)) {
                                    continue;
                                }
                                let name = item.ident.name.to_ident_string();
                                v.push((name, item.span));
                            }
                        }
                        ItemKind::Enum(_, _) | ItemKind::Struct(_, _) | ItemKind::Union(_, _) => {
                            types.entry(name).or_default().push((p, item.span));
                        }
                        ItemKind::Impl(i) => {
                            if let TyKind::Path(QPath::Resolved(_, path)) = &i.self_ty.kind {
                                let seg = path.segments.last().unwrap();
                                let name = seg.ident.name.to_ident_string().to_string();
                                let span = source_map.span_extend_to_line(item.span);
                                impls.insert((p, name), span);
                            }
                        }
                        _ => {}
                    }
                }

                let mut suggestions: BTreeMap<_, Vec<_>> = BTreeMap::new();

                for (p, fs) in foreigns {
                    let mut v = vec![];

                    let fspan = fspans.get(&p).unwrap();
                    let (rps, spans): (Vec<_>, Vec<_>) = fs
                        .into_iter()
                        .filter_map(|(f, span)| functions.get(&f).map(|rp| (rp, span)))
                        .unzip();

                    for rp in rps {
                        let stmt = format!("use {};\n", rp);
                        let snippet = compile_util::span_to_snippet(*fspan, source_map);
                        let suggestion = compile_util::make_suggestion(snippet, &stmt);
                        v.push(suggestion);
                    }

                    for span in spans {
                        let snippet = compile_util::span_to_snippet(span, source_map);
                        let suggestion = compile_util::make_suggestion(snippet, "");
                        v.push(suggestion);
                    }

                    if !v.is_empty() {
                        suggestions.insert(p.clone(), v);
                    }
                }

                for (name, mut ts) in types {
                    let path = ts.pop().unwrap().0;
                    let rp = mk_rust_path(&dir, &path, &name);
                    for (path, span) in ts {
                        let v = suggestions.entry(path.clone()).or_default();

                        let fspan = fspans.get(&path).unwrap();
                        let stmt = format!("use {};\n", rp);
                        let snippet = compile_util::span_to_snippet(*fspan, source_map);
                        let suggestion = compile_util::make_suggestion(snippet, &stmt);
                        v.push(suggestion);

                        let impl_span = impls.get(&(path.clone(), name.clone())).unwrap();
                        let span = span.with_lo(impl_span.lo());
                        let snippet = compile_util::span_to_snippet(span, source_map);
                        let suggestion = compile_util::make_suggestion(snippet, "");
                        v.push(suggestion);
                    }
                }

                suggestions
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

fn mk_rust_path(dir: &Path, path: &Path, name: &str) -> String {
    let mut path = path.strip_prefix(dir).unwrap().to_path_buf();
    path.set_extension("");
    std::iter::once("crate")
        .chain(path.components().map(|c| c.as_os_str().to_str().unwrap()))
        .chain(std::iter::once(name))
        .intersperse("::")
        .collect()
}
