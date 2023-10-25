use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};

use etrace::some_or;
use rustc_ast::LitKind;
use rustc_hir::{
    def::Res, intravisit::Visitor as HVisitor, BinOpKind, Expr, ExprKind, FnRetTy, HirId, ItemKind,
    PatKind, QPath, UnOp,
};
use rustc_middle::{hir::nested_filter, ty::TyCtxt};
use rustc_span::{source_map::SourceMap, BytePos, Span};
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
        if let ItemKind::Fn(sig, _, body_id) = item.kind {
            let def_id = id.owner_id.to_def_id();
            let name = tcx.def_path_str(def_id);
            let body = hir.body(body_id);

            let mut visitor = BodyVisitor::new(tcx);
            visitor.visit_body(body);

            let mut call_spans = BTreeSet::new();

            for if_call in visitor.if_calls {
                let IfCall {
                    if_span,
                    call,
                    n,
                    eq,
                    t_span,
                    f_span,
                } = if_call;
                let Call { span, callee, args } = call;
                if let Some(params) = param_map.get(&callee) {
                    let (sv, _) = SuccValue::find(params);
                    let t_succ = match sv {
                        SuccValue::Int(i) => (n as i128 == i) == eq,
                        SuccValue::Uint(i) => (n == i) == eq,
                        SuccValue::Bool(_) => todo!(),
                        SuccValue::None => continue,
                    };
                    call_spans.insert(span);

                    v.extend(remove_args(params, &args, source_map));

                    let if_span = if_span.shrink_to_lo().with_hi(span.lo());
                    let snippet = compile_util::span_to_snippet(if_span, source_map);
                    let suggestion = compile_util::make_suggestion(snippet, "match ".to_string());
                    v.push(suggestion);

                    let bt_span = t_span.with_lo(span.hi()).with_hi(t_span.lo());
                    let snippet = compile_util::span_to_snippet(bt_span, source_map);
                    let pat = if t_succ {
                        " { Some(_) => "
                    } else {
                        " { None => "
                    };
                    let suggestion = compile_util::make_suggestion(snippet, pat.to_string());
                    v.push(suggestion);

                    if let Some(f_span) = f_span {
                        let else_span = t_span.with_lo(t_span.hi()).with_hi(f_span.lo());
                        let snippet = compile_util::span_to_snippet(else_span, source_map);
                        let pat = if t_succ {
                            "\n    None => "
                        } else {
                            "\n    Some(_) => "
                        };
                        let suggestion = compile_util::make_suggestion(snippet, pat.to_string());
                        v.push(suggestion);

                        let end_span = f_span.with_lo(f_span.hi());
                        let snippet = compile_util::span_to_snippet(end_span, source_map);
                        let suggestion = compile_util::make_suggestion(snippet, " }".to_string());
                        v.push(suggestion);
                    } else {
                        let else_span = t_span.with_lo(t_span.hi());
                        let snippet = compile_util::span_to_snippet(else_span, source_map);
                        let arm = if t_succ {
                            "\n    None => {} }"
                        } else {
                            "\n    Some(_) => {} }"
                        };
                        let suggestion = compile_util::make_suggestion(snippet, arm.to_string());
                        v.push(suggestion);
                    }
                }
            }

            for call in visitor.calls {
                let Call { span, callee, args } = call;
                if call_spans.contains(&span) {
                    continue;
                }
                if let Some(params) = param_map.get(&callee) {
                    v.extend(remove_args(params, &args, source_map));

                    let snippet = compile_util::span_to_snippet(span.shrink_to_lo(), source_map);
                    let vars = (0..=params.len()).map(|i| format!("rv___{}", i));
                    let binding = mk_string(vars, "{ let (", ", ", ") = ");
                    let suggestion = compile_util::make_suggestion(snippet, binding);
                    v.push(suggestion);

                    let assigns = params.iter().enumerate().map(|(i, param)| {
                        let (arg, is_null) = args[param.index - 1];
                        let arg = source_map.span_to_snippet(arg).unwrap();
                        if !is_null {
                            if param.must {
                                format!("*({}) = rv___{};", arg, i + 1)
                            } else {
                                format!("if let Some(v) = rv___{} {{ *({}) = v; }}", i + 1, arg)
                            }
                        } else {
                            "".to_string()
                        }
                    });
                    let assign = mk_string(assigns, "; ", " ", " rv___0 }");

                    let snippet = compile_util::span_to_snippet(span.shrink_to_hi(), source_map);
                    let suggestion = compile_util::make_suggestion(snippet, assign);
                    v.push(suggestion);
                }
            }

            if let Some(params) = param_map.get(&name) {
                let (_, indices) = SuccValue::find(params);
                let body_params: Vec<_> = body
                    .params
                    .iter()
                    .enumerate()
                    .map(|(i, param)| {
                        if let PatKind::Binding(_, hir_id, ident, _) = param.pat.kind {
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
                            (span, hir_id, name)
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
                    let ret_ty = if indices.is_empty() {
                        let tys =
                            std::iter::once(ty).chain(params.iter().map(|(param, _, _, _, ty)| {
                                if param.must {
                                    ty.to_string()
                                } else {
                                    format!("Option<{}>", ty)
                                }
                            }));
                        mk_string(tys, "(", ", ", ")")
                    } else {
                        let tys = indices.iter().map(|i| {
                            let (_, _, _, _, ty) = params
                                .iter()
                                .find(|(param, _, _, _, _)| param.index == *i)
                                .unwrap();
                            ty
                        });
                        let opt = mk_string(tys, "Option<(", ", ", ")>");
                        let tys = std::iter::once(opt).chain(params.iter().filter_map(
                            |(param, _, _, _, ty)| {
                                if indices.contains(&param.index) {
                                    return None;
                                }
                                let ty = if param.must {
                                    ty.to_string()
                                } else {
                                    format!("Option<{}>", ty)
                                };
                                Some(ty)
                            },
                        ));
                        mk_string(tys, "(", ", ", ")")
                    };
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

fn remove_args(
    params: &[OutputParam],
    args: &[(Span, bool)],
    source_map: &SourceMap,
) -> Vec<Suggestion> {
    let mut v = vec![];
    for param in params {
        let (span, _) = args[param.index - 1];
        let span = if param.index == args.len() {
            if let Some(comma_span) = source_map.span_look_ahead(span, ",", Some(1)) {
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
    v
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
    args: Vec<(Span, bool)>,
}

#[derive(Debug)]
struct IfCall {
    if_span: Span,
    call: Call,
    n: u128,
    eq: bool,
    t_span: Span,
    f_span: Option<Span>,
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

struct BodyVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    returns: Vec<Return>,
    calls: Vec<Call>,
    if_calls: Vec<IfCall>,
    indirect_assigns: Vec<IndirectAssign>,
    null_checks: Vec<NullCheck>,
}

impl<'tcx> BodyVisitor<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            returns: vec![],
            calls: vec![],
            if_calls: vec![],
            indirect_assigns: vec![],
            null_checks: vec![],
        }
    }

    fn try_into_call(&self, expr: &Expr<'_>, callee: &Expr<'_>, args: &[Expr<'_>]) -> Option<Call> {
        if let Some(path) = expr_to_path(callee) {
            if let Res::Def(_, def_id) = path.res {
                let span = expr.span;
                let callee = self.tcx.def_path_str(def_id);
                let args = args
                    .iter()
                    .map(|arg| {
                        let is_null = as_int_lit(arg).map(|n| n == 0).unwrap_or(false);
                        (arg.span, is_null)
                    })
                    .collect();
                return Some(Call { span, callee, args });
            }
        }
        None
    }
}

impl<'tcx> HVisitor<'tcx> for BodyVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.tcx.hir()
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        match expr.kind {
            ExprKind::Ret(e) => {
                let span = expr.span;
                let value = e.as_ref().map(|e| e.span);
                self.returns.push(Return { span, value });
            }
            ExprKind::Call(callee, args) => {
                if let Some(call) = self.try_into_call(expr, callee, args) {
                    self.calls.push(call);
                }
            }
            ExprKind::If(c, t, f) => {
                if let ExprKind::Binary(op, lhs, rhs) = remove_cast_and_drop_temps(c).kind {
                    let eq = match op.node {
                        BinOpKind::Eq => Some(true),
                        BinOpKind::Ne => Some(false),
                        _ => None,
                    };
                    if let Some(eq) = eq {
                        let t_span = t.span;
                        let f_span = f.map(|f| f.span);
                        let lhs = remove_cast_and_drop_temps(lhs);
                        let rhs = remove_cast_and_drop_temps(rhs);
                        let call_n = if let (ExprKind::Call(callee, args), Some(n)) =
                            (lhs.kind, as_int_lit(rhs))
                        {
                            self.try_into_call(lhs, callee, args).map(|call| (call, n))
                        } else if let (ExprKind::Call(callee, args), Some(n)) =
                            (rhs.kind, as_int_lit(lhs))
                        {
                            self.try_into_call(rhs, callee, args).map(|call| (call, n))
                        } else {
                            None
                        };
                        if let Some((call, n)) = call_n {
                            let if_span = expr.span;
                            self.if_calls.push(IfCall {
                                if_span,
                                call,
                                n,
                                eq,
                                t_span,
                                f_span,
                            });
                        }
                    }
                }
            }
            ExprKind::Assign(lhs, rhs, _) => {
                if let ExprKind::Unary(UnOp::Deref, ptr) = lhs.kind {
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum SuccValue {
    None,
    Int(i128),
    Uint(u128),
    Bool(bool),
}

impl SuccValue {
    fn new(rvs: &ReturnValues) -> Self {
        match rvs {
            ReturnValues::Int(succ, fail) => {
                let succ = some_or!(succ.gamma(), return Self::None);
                if succ.len() != 1 {
                    return Self::None;
                }
                let fail = some_or!(fail.gamma(), return Self::None);
                if !succ.is_disjoint(fail) {
                    return Self::None;
                }
                Self::Int(*succ.first().unwrap())
            }
            ReturnValues::Uint(succ, fail) => {
                let succ = some_or!(succ.gamma(), return Self::None);
                if succ.len() != 1 {
                    return Self::None;
                }
                let fail = some_or!(fail.gamma(), return Self::None);
                if !succ.is_disjoint(fail) {
                    return Self::None;
                }
                Self::Uint(*succ.first().unwrap())
            }
            ReturnValues::Bool(succ, fail) => {
                let succ = succ.gamma();
                if succ.len() != 1 {
                    return Self::None;
                }
                let succ = succ.first().unwrap();
                let fail = fail.gamma();
                if fail.len() != 1 {
                    return Self::None;
                }
                let fail = fail.first().unwrap();
                if succ == fail {
                    return Self::None;
                }
                Self::Bool(*succ)
            }
            _ => Self::None,
        }
    }

    fn find(params: &[OutputParam]) -> (Self, Vec<usize>) {
        let v: Vec<_> = params
            .iter()
            .filter_map(|param| {
                if !param.must {
                    Some((param.index, Self::new(&param.return_values)))
                } else {
                    None
                }
            })
            .collect();
        let mut vs: BTreeSet<_> = v.iter().map(|(_, v)| *v).collect();
        if vs.len() == 1 {
            (
                vs.pop_first().unwrap(),
                v.into_iter().map(|(i, _)| i).collect(),
            )
        } else {
            (Self::None, vec![])
        }
    }
}

fn expr_to_path<'a, 'tcx>(expr: &'a Expr<'tcx>) -> Option<&'a rustc_hir::Path<'tcx>> {
    if let ExprKind::Path(QPath::Resolved(_, path)) = expr.kind {
        Some(path)
    } else {
        None
    }
}

fn remove_cast_and_drop_temps<'a, 'tcx>(expr: &'a Expr<'tcx>) -> &'a Expr<'tcx> {
    if let ExprKind::Cast(expr, _) | ExprKind::DropTemps(expr) = expr.kind {
        remove_cast_and_drop_temps(expr)
    } else {
        expr
    }
}

fn as_int_lit(expr: &Expr<'_>) -> Option<u128> {
    if let ExprKind::Lit(lit) = expr.kind {
        if let LitKind::Int(n, _) = lit.node {
            return Some(n);
        }
    }
    None
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
