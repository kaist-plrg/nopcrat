use std::{
    collections::BTreeMap,
    path::{Path, PathBuf},
};

use etrace::some_or;
use rustc_hir::{
    def::Res, intravisit::Visitor as HVisitor, Expr, ExprKind, FnRetTy, HirId, ItemKind, PatKind,
    QPath, UnOp,
};
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
    param_map: &BTreeMap<String, Vec<OutputParam>>,
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

            let mut visitor = BodyVisitor::new(tcx);
            visitor.visit_body(body);

            for call in visitor.calls {
                let Call { span, callee, args } = call;
                if let Some(params) = param_map.get(&callee) {
                    for param in params {
                        let span = args[param.index - 1];
                        let span = if param.index == args.len() {
                            if let Some(comma_span) = source_map.span_look_ahead(span, ",", Some(1))
                            {
                                span.with_hi(comma_span.hi())
                            } else {
                                span
                            }
                        } else {
                            span.with_hi(span.hi() + BytePos(1))
                        };
                        let snippet = compile_util::span_to_snippet(span, source_map);
                        let suggestion = compile_util::make_suggestion(snippet, "".to_string());
                        v.push(suggestion);
                    }

                    let snippet = compile_util::span_to_snippet(span.shrink_to_lo(), source_map);
                    let vars = (0..=params.len()).map(|i| format!("rv___{}", i));
                    let binding = mk_string(vars, "{ let (", ", ", ") = ");
                    let suggestion = compile_util::make_suggestion(snippet, binding);
                    v.push(suggestion);

                    let assigns = params.iter().enumerate().map(|(i, param)| {
                        let arg = args[param.index - 1];
                        let arg = source_map.span_to_snippet(arg).unwrap();
                        if param.must {
                            format!("*({}) = rv___{};", arg, i + 1)
                        } else {
                            format!("if let Some(v) = rv___{} {{ *({}) = v; }}", i + 1, arg)
                        }
                    });
                    let assign = mk_string(assigns, "; ", " ", " rv___0 }");

                    let snippet = compile_util::span_to_snippet(span.shrink_to_hi(), source_map);
                    let suggestion = compile_util::make_suggestion(snippet, assign);
                    v.push(suggestion);
                }
            }

            if let Some(params) = param_map.get(&name) {
                let body_params: Vec<_> = body
                    .params
                    .iter()
                    .enumerate()
                    .map(|(i, param)| {
                        if let PatKind::Binding(_, hir_id, ident, _) = &param.pat.kind {
                            let span = if i == body.params.len() - 1 {
                                if let Some(comma_span) =
                                    source_map.span_look_ahead(param.span, ",", Some(1))
                                {
                                    param.span.with_hi(comma_span.hi())
                                } else {
                                    param.span
                                }
                            } else {
                                param.span.with_hi(param.span.hi() + BytePos(1))
                            };
                            let name = ident.name.to_ident_string();
                            (span, *hir_id, name)
                        } else {
                            unreachable!()
                        }
                    })
                    .collect();

                let params: Vec<_> = params
                    .iter()
                    .map(|param| {
                        let index = param.index - 1;
                        let (span, hir_id, name) = &body_params[index];
                        let ty = source_map
                            .span_to_snippet(sig.decl.inputs[index].span)
                            .unwrap()
                            .strip_prefix("*mut ")
                            .unwrap()
                            .to_string();
                        (param, *span, *hir_id, name.as_str(), ty)
                    })
                    .collect();

                for (_, span, _, _, _) in &params {
                    let snippet = compile_util::span_to_snippet(*span, source_map);
                    let suggestion = compile_util::make_suggestion(snippet, "".to_string());
                    v.push(suggestion);
                }

                if let FnRetTy::Return(ty) = sig.decl.output {
                    let span = ty.span;
                    let ty = source_map.span_to_snippet(span).unwrap();
                    let tys: String = std::iter::once(ty)
                        .chain(params.iter().map(|(param, _, _, _, ty)| {
                            if param.must {
                                format!(", {}", ty)
                            } else {
                                format!(", Option<{}>", ty)
                            }
                        }))
                        .collect();
                    let ret_ty = format!("({})", tys);
                    let snippet = compile_util::span_to_snippet(span, source_map);
                    let suggestion = compile_util::make_suggestion(snippet, ret_ty);
                    v.push(suggestion);
                } else {
                    todo!();
                }

                let local_vars: String = params
                    .iter()
                    .map(|(param, _, _, name, ty)| {
                        if param.must {
                            format!(
                                "
    let mut {0}___v: {1} = std::mem::transmute([0u8; std::mem::size_of::<{1}>()]);
    let {0}: *mut {1} = &mut {0}___v;",
                                name, ty,
                            )
                        } else {
                            format!(
                                "
    let mut {0}___v: Option<{1}> = None;",
                                name, ty,
                            )
                        }
                    })
                    .collect();

                let pos = body.value.span.lo() + BytePos(1);
                let span = body.value.span.with_lo(pos).with_hi(pos);
                let snippet = compile_util::span_to_snippet(span, source_map);
                let suggestion = compile_util::make_suggestion(snippet, local_vars);
                v.push(suggestion);

                for ret in visitor.returns {
                    let Return { span, value } = ret;
                    let mut values = vec![];
                    if let Some(value) = value {
                        let value = source_map.span_to_snippet(value).unwrap();
                        values.push(value);
                    }
                    for (_, _, _, name, _) in &params {
                        values.push(format!("{}___v", name));
                    }
                    let values: String = values.join(", ");
                    let ret = format!("return ({})", values);
                    let snippet = compile_util::span_to_snippet(span, source_map);
                    let suggestion = compile_util::make_suggestion(snippet, ret);
                    v.push(suggestion);
                }

                for assign in visitor.indirect_assigns {
                    let IndirectAssign {
                        lhs_span,
                        lhs,
                        rhs_span,
                    } = assign;
                    let (param, _, _, name, _) = some_or!(
                        params.iter().find(|(_, _, hir_id, _, _)| *hir_id == lhs),
                        continue
                    );
                    if param.must {
                        continue;
                    }

                    let lhs = format!("{}___v", name);
                    let snippet = compile_util::span_to_snippet(lhs_span, source_map);
                    let suggestion = compile_util::make_suggestion(snippet, lhs);
                    v.push(suggestion);

                    let rhs = source_map.span_to_snippet(rhs_span).unwrap();
                    let rhs = format!("Some({})", rhs);
                    let snippet = compile_util::span_to_snippet(rhs_span, source_map);
                    let suggestion = compile_util::make_suggestion(snippet, rhs);
                    v.push(suggestion);
                }

                for check in visitor.null_checks {
                    let NullCheck { span, hir_id } = check;
                    if !params.iter().any(|(_, _, id, _, _)| *id == hir_id) {
                        continue;
                    }
                    let snippet = compile_util::span_to_snippet(span, source_map);
                    let suggestion = compile_util::make_suggestion(snippet, "false".to_string());
                    v.push(suggestion);
                }
            }
        }
    }
    suggestions.retain(|_, v| !v.is_empty());
    suggestions
}

struct BodyVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    returns: Vec<Return>,
    calls: Vec<Call>,
    indirect_assigns: Vec<IndirectAssign>,
    null_checks: Vec<NullCheck>,
}

#[derive(Debug)]
struct Return {
    span: Span,
    value: Option<Span>,
}

#[derive(Debug)]
struct Call {
    span: Span,
    callee: String,
    args: Vec<Span>,
}

#[derive(Debug)]
struct IndirectAssign {
    lhs_span: Span,
    lhs: HirId,
    rhs_span: Span,
}

#[derive(Debug)]
struct NullCheck {
    span: Span,
    hir_id: HirId,
}

impl<'tcx> BodyVisitor<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            returns: vec![],
            calls: vec![],
            indirect_assigns: vec![],
            null_checks: vec![],
        }
    }
}

impl<'tcx> HVisitor<'tcx> for BodyVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.tcx.hir()
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        match &expr.kind {
            ExprKind::Ret(e) => {
                let span = expr.span;
                let value = e.as_ref().map(|e| e.span);
                self.returns.push(Return { span, value });
            }
            ExprKind::Call(callee, args) => {
                let span = expr.span;
                if let Some(path) = expr_to_path(callee) {
                    if let Res::Def(_, def_id) = path.res {
                        let callee = self.tcx.def_path_str(def_id);
                        let args = args.iter().map(|arg| arg.span).collect();
                        self.calls.push(Call { span, callee, args });
                    }
                }
            }
            ExprKind::Assign(lhs, rhs, _) => {
                if let ExprKind::Unary(UnOp::Deref, ptr) = &lhs.kind {
                    if let Some(path) = expr_to_path(ptr) {
                        if let Res::Local(hir_id) = path.res {
                            self.indirect_assigns.push(IndirectAssign {
                                lhs_span: lhs.span,
                                lhs: hir_id,
                                rhs_span: rhs.span,
                            });
                        }
                    }
                }
            }
            ExprKind::MethodCall(seg, v, _, _) => {
                if seg.ident.name.to_ident_string() == "is_null" {
                    if let Some(path) = expr_to_path(v) {
                        if let Res::Local(hir_id) = path.res {
                            self.null_checks.push(NullCheck {
                                span: expr.span,
                                hir_id,
                            });
                        }
                    }
                }
            }
            _ => {}
        }
        rustc_hir::intravisit::walk_expr(self, expr);
    }
}

fn expr_to_path<'a, 'tcx>(expr: &'a Expr<'tcx>) -> Option<&'a rustc_hir::Path<'tcx>> {
    if let ExprKind::Path(QPath::Resolved(_, path)) = &expr.kind {
        Some(*path)
    } else {
        None
    }
}

fn mk_string<S: AsRef<str>, I: Iterator<Item = S>>(
    iter: I,
    start: &str,
    sep: &str,
    end: &str,
) -> String {
    let mut s = start.to_string();
    for (i, item) in iter.enumerate() {
        if i > 0 {
            s.push_str(sep);
        }
        s.push_str(item.as_ref());
    }
    s.push_str(end);
    s
}
