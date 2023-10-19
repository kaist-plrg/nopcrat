use std::{
    collections::BTreeMap,
    path::{Path, PathBuf},
};

use etrace::some_or;
use rustc_hir::{intravisit::Visitor as HVisitor, Expr, ExprKind, FnRetTy, ItemKind, PatKind};
use rustc_middle::{hir::nested_filter, ty::TyCtxt};
use rustc_span::{BytePos, Span};
use rustfix::Suggestion;

use crate::{ai::analysis::*, compile_util};

pub fn transform_path(path: &Path, params: &BTreeMap<String, Vec<OutputParam>>) {
    let input = compile_util::path_to_input(path);
    let config = compile_util::make_config(input);
    let suggestions = compile_util::run_compiler(config, |tcx| transform(tcx, params)).unwrap();
    compile_util::apply_suggestions(&suggestions);
}

fn transform(
    tcx: TyCtxt<'_>,
    params: &BTreeMap<String, Vec<OutputParam>>,
) -> BTreeMap<PathBuf, Vec<Suggestion>> {
    let hir = tcx.hir();
    let source_map = tcx.sess.source_map();
    let mut suggestions = BTreeMap::new();
    for id in hir.items() {
        let item = hir.item(id);
        let file = some_or!(compile_util::span_to_path(item.span, source_map), continue);
        let v = suggestions.entry(file).or_insert_with(Vec::new);
        if let ItemKind::Fn(sig, _, body_id) = &item.kind {
            let def_id = id.owner_id.to_def_id();
            let name = tcx.def_path_str(def_id);
            let body = hir.body(*body_id);
            if let Some(params) = params.get(&name) {
                let body_params: BTreeMap<_, _> = body
                    .params
                    .iter()
                    .enumerate()
                    .map(|(i, param)| {
                        if let PatKind::Binding(_, _, ident, _) = &param.pat.kind {
                            let span = if i == body.params.len() - 1 {
                                if let Some(comma_span) =
                                    source_map.span_look_ahead(param.span, ",", Some(1))
                                {
                                    param.span.with_hi(comma_span.hi())
                                } else {
                                    param.span
                                }
                            } else {
                                source_map.span_extend_to_next_char(param.span, ',', true)
                            };
                            let name = ident.name.to_ident_string();
                            (i, (span, name))
                        } else {
                            unreachable!()
                        }
                    })
                    .collect();

                let params: Vec<_> = params
                    .iter()
                    .map(|param| {
                        let index = param.index - 1;
                        let (span, name) = body_params.get(&index).unwrap();
                        let ty = source_map
                            .span_to_snippet(sig.decl.inputs[index].span)
                            .unwrap()
                            .strip_prefix("*mut ")
                            .unwrap()
                            .to_string();
                        (param, *span, name.as_str(), ty)
                    })
                    .collect();

                for (_, span, _, _) in &params {
                    let snippet = compile_util::span_to_snippet(*span, source_map);
                    let suggestion = compile_util::make_suggestion(snippet, "");
                    v.push(suggestion);
                }

                if let FnRetTy::Return(ty) = sig.decl.output {
                    let span = ty.span;
                    let ty = source_map.span_to_snippet(span).unwrap();
                    let tys: String = std::iter::once(ty)
                        .chain(params.iter().map(|(_, _, _, ty)| format!(", {}", ty)))
                        .collect();
                    let ret_ty = format!("({})", tys);
                    let snippet = compile_util::span_to_snippet(span, source_map);
                    let suggestion = compile_util::make_suggestion(snippet, &ret_ty);
                    v.push(suggestion);
                } else {
                    todo!();
                }

                let local_vars: String = params
                    .iter()
                    .map(|(param, _, name, ty)| {
                        if param.must {
                            format!(
                                "
    let mut {0}___v: {1} = std::mem::transmute([0u8; std::mem::size_of::<{1}>()]);
    let {0}: *mut {1} = &mut {0}___v;",
                                name, ty,
                            )
                        } else {
                            todo!()
                        }
                    })
                    .collect();

                let pos = body.value.span.lo() + BytePos(1);
                let span = body.value.span.with_lo(pos).with_hi(pos);
                let snippet = compile_util::span_to_snippet(span, source_map);
                let suggestion = compile_util::make_suggestion(snippet, &local_vars);
                v.push(suggestion);

                let mut visitor = RetVisitor::new(tcx);
                visitor.visit_body(body);
                for (span, ret_v) in visitor.returns {
                    let mut values = vec![];
                    if let Some(ret_v) = ret_v {
                        values.push(ret_v);
                    }
                    for (_, _, name, _) in &params {
                        values.push(format!("{}___v", name));
                    }
                    let values: String = values.join(", ");
                    let ret = format!("return ({})", values);
                    let snippet = compile_util::span_to_snippet(span, source_map);
                    let suggestion = compile_util::make_suggestion(snippet, &ret);
                    v.push(suggestion);
                }
            }
        }
    }
    suggestions.retain(|_, v| !v.is_empty());
    suggestions
}

struct RetVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    returns: Vec<(Span, Option<String>)>,
}

impl<'tcx> RetVisitor<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            returns: vec![],
        }
    }
}

impl<'tcx> HVisitor<'tcx> for RetVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.tcx.hir()
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        if let ExprKind::Ret(e) = &expr.kind {
            let span = expr.span;
            let ret_v = e
                .as_ref()
                .map(|e| self.tcx.sess.source_map().span_to_snippet(e.span).unwrap());
            self.returns.push((span, ret_v));
        }
        rustc_hir::intravisit::walk_expr(self, expr);
    }
}
