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
use rustc_span::{def_id::DefId, source_map::SourceMap, BytePos, Span};
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

    let mut funcs = BTreeMap::new();
    for id in hir.items() {
        let item = hir.item(id);
        let ItemKind::Fn(sig, _, body_id) = item.kind else {
            continue;
        };
        let def_id = id.owner_id.to_def_id();
        let name = tcx.def_path_str(def_id);
        let params = some_or!(param_map.get(&name), continue);
        let body = hir.body(body_id);
        let index_map: BTreeMap<_, _> = params
            .iter()
            .map(|param| {
                let OutputParam { index, must, .. } = param;
                let param = &body.params[*index];
                let PatKind::Binding(_, hir_id, ident, _) = param.pat.kind else {
                    unreachable!()
                };
                let span = to_comma(param.span, source_map);
                let name = ident.name.to_ident_string();
                let ty = source_map
                    .span_to_snippet(sig.decl.inputs[*index].span)
                    .unwrap()
                    .strip_prefix("*mut ")
                    .unwrap()
                    .to_string();
                let param = Param {
                    index: *index,
                    must: *must,
                    name,
                    ty,
                    span,
                    hir_id,
                };
                (*index, param)
            })
            .collect();
        let hir_id_map: BTreeMap<_, _> = index_map
            .values()
            .cloned()
            .map(|param| (param.hir_id, param))
            .collect();
        let (succ_value, first_return) = SuccValue::find(params);
        let remaining_return: Vec<_> = index_map
            .keys()
            .copied()
            .filter(|i| !first_return.contains(i))
            .collect();
        let is_unit = matches!(sig.decl.output, FnRetTy::DefaultReturn(_));
        let func = Func {
            is_unit,
            succ_value,
            first_return,
            remaining_return,
            index_map,
            hir_id_map,
        };
        funcs.insert(def_id, func);
    }

    let mut suggestions: BTreeMap<_, Vec<_>> = BTreeMap::new();
    for id in hir.items() {
        let item = hir.item(id);
        let ItemKind::Fn(sig, _, body_id) = item.kind else {
            continue;
        };

        let file = some_or!(compile_util::span_to_path(item.span, source_map), continue);
        let v = suggestions.entry(file).or_default();
        let mut fix = |span, code| {
            let snippet = compile_util::span_to_snippet(span, source_map);
            let suggestion = compile_util::make_suggestion(snippet, code);
            v.push(suggestion);
        };

        let def_id = id.owner_id.to_def_id();
        let body = hir.body(body_id);

        let mut visitor = BodyVisitor::new(tcx);
        visitor.visit_body(body);

        // let mut call_spans = BTreeSet::new();

        // for if_call in visitor.if_calls {
        //     let IfCall {
        //         if_span,
        //         call,
        //         n,
        //         eq,
        //         t_span,
        //         f_span,
        //     } = if_call;
        //     let Call { span, callee, args } = call;
        //     let func = some_or!(funcs.get(&callee), continue);
        //     let t_succ = match func.succ_value {
        //         SuccValue::Int(i) => (n as i128 == i) == eq,
        //         SuccValue::Uint(i) => (n == i) == eq,
        //         SuccValue::Bool(_) => todo!(),
        //         SuccValue::None => continue,
        //     };
        //     call_spans.insert(span);

        //     for index in func.index_map.keys() {
        //         let span = to_comma(args[*index].0, source_map);
        //         fix(span, "".to_string());
        //     }

        //     let if_span = if_span.shrink_to_lo().with_hi(span.lo());
        //     fix(if_span, "match ".to_string());

        //     let bt_span = t_span.with_lo(span.hi()).with_hi(t_span.lo());
        //     let pat = if t_succ {
        //         " { Some(_) => "
        //     } else {
        //         " { None => "
        //     };
        //     fix(bt_span, pat.to_string());

        //     if let Some(f_span) = f_span {
        //         let else_span = t_span.with_lo(t_span.hi()).with_hi(f_span.lo());
        //         let pat = if t_succ {
        //             "\n    None => "
        //         } else {
        //             "\n    Some(_) => "
        //         };
        //         fix(else_span, pat.to_string());

        //         let end_span = f_span.with_lo(f_span.hi());
        //         fix(end_span, "}".to_string());
        //     } else {
        //         let else_span = t_span.with_lo(t_span.hi());
        //         let arm = if t_succ {
        //             "\n    None => {} }"
        //         } else {
        //             "\n    Some(_) => {} }"
        //         };
        //         fix(else_span, arm.to_string());
        //     }
        // }

        for call in visitor.calls {
            let Call { span, callee, args } = call;
            // if call_spans.contains(&span) {
            //     continue;
            // }
            let func = some_or!(funcs.get(&callee), continue);

            for index in func.index_map.keys() {
                let span = to_comma(args[*index].0, source_map);
                fix(span, "".to_string());
            }

            let start = if func.is_unit { 1 } else { 0 };
            let vars = (start..=func.index_map.len()).map(|i| format!("rv___{}", i));
            let binding = mk_string(vars, "{ let (", ", ", ") = ");
            fix(span.shrink_to_lo(), binding);

            let assigns = func.params().enumerate().map(|(i, param)| {
                let (arg, is_null) = args[param.index];
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
            let res = if func.is_unit { " }" } else { " rv___0 }" };
            let assign = mk_string(assigns, "; ", " ", res);
            fix(span.shrink_to_hi(), assign);
        }

        let func = some_or!(funcs.get(&def_id), continue);
        for param in func.params() {
            fix(param.span, "".to_string());
        }

        match sig.decl.output {
            FnRetTy::Return(ty) => {
                let span = ty.span;
                let ty = source_map.span_to_snippet(span).unwrap();
                let tys = std::iter::once(ty).chain(func.params().map(|param| {
                    if param.must {
                        param.ty.to_string()
                    } else {
                        format!("Option<{}>", param.ty)
                    }
                }));
                let ret_ty = mk_string(tys, "(", ", ", ")");
                // let ret_ty = if func.first_return.is_empty() {
                //     let tys = std::iter::once(ty).chain(func.params().map(|param| {
                //         if param.must {
                //             param.ty.to_string()
                //         } else {
                //             format!("Option<{}>", param.ty)
                //         }
                //     }));
                //     mk_string(tys, "(", ", ", ")")
                // } else {
                //     let tys = func
                //         .first_return
                //         .iter()
                //         .map(|i| func.index_map[i].ty.clone());
                //     let opt = mk_string(tys, "Option<(", ", ", ")>");
                //     let tys = std::iter::once(opt).chain(func.remaining_return.iter().map(|i| {
                //         let param = &func.index_map[i];
                //         if param.must {
                //             param.ty.to_string()
                //         } else {
                //             format!("Option<{}>", param.ty)
                //         }
                //     }));
                //     mk_string(tys, "(", ", ", ")")
                // };
                fix(span, ret_ty);
            }
            FnRetTy::DefaultReturn(span) => {
                let tys = func.params().map(|param| {
                    if param.must {
                        param.ty.to_string()
                    } else {
                        format!("Option<{}>", param.ty)
                    }
                });
                let ret_ty = mk_string(tys, "-> (", ", ", ")");
                fix(span, ret_ty);
            }
        }

        let local_vars: String = func
            .params()
            .map(|param| {
                if param.must {
                    format!(
                        "
    let mut {0}___v: {1} = std::mem::transmute([0u8; std::mem::size_of::<{1}>()]);
    let {0}: *mut {1} = &mut {0}___v;",
                        param.name, param.ty,
                    )
                } else {
                    format!(
                        "
    let mut {0}___v: Option<{1}> = None;",
                        param.name, param.ty,
                    )
                }
            })
            .collect();

        let pos = body.value.span.lo() + BytePos(1);
        let span = body.value.span.with_lo(pos).with_hi(pos);
        fix(span, local_vars);

        for ret in visitor.returns {
            let Return { span, value } = ret;
            let mut values = vec![];
            if let Some(value) = value {
                let value = source_map.span_to_snippet(value).unwrap();
                values.push(value);
            }
            for param in func.params() {
                values.push(format!("{}___v", param.name));
            }
            let values: String = values.join(", ");
            let ret = format!("return ({})", values);
            fix(span, ret);
        }

        if func.is_unit {
            let mut values = vec![];
            for param in func.params() {
                values.push(format!("{}___v", param.name));
            }
            let values: String = values.join(", ");
            let ret = format!("({})", values);

            let pos = body.value.span.hi() - BytePos(1);
            let span = body.value.span.with_lo(pos).with_hi(pos);
            fix(span, ret);
        }

        for assign in visitor.indirect_assigns {
            let IndirectAssign {
                lhs_span,
                lhs,
                rhs_span,
            } = assign;
            let param = some_or!(func.hir_id_map.get(&lhs), continue);
            if param.must {
                continue;
            }

            let lhs = format!("{}___v", param.name);
            fix(lhs_span, lhs);

            let rhs = source_map.span_to_snippet(rhs_span).unwrap();
            let rhs = format!("Some({})", rhs);
            fix(rhs_span, rhs);
        }

        for check in visitor.null_checks {
            let NullCheck { span, hir_id } = check;
            if !func.hir_id_map.contains_key(&hir_id) {
                continue;
            }
            fix(span, "false".to_string());
        }
    }
    suggestions.retain(|_, v| !v.is_empty());
    for suggestions in suggestions.values_mut() {
        suggestions.sort_by_key(|s| s.snippets[0].range.start);
    }
    suggestions
}

#[derive(Debug, Clone)]
struct Param {
    index: usize,
    must: bool,
    span: Span,
    hir_id: HirId,
    name: String,
    ty: String,
}

#[allow(unused)]
struct Func {
    is_unit: bool,
    succ_value: SuccValue,
    first_return: Vec<usize>,
    remaining_return: Vec<usize>,
    index_map: BTreeMap<usize, Param>,
    hir_id_map: BTreeMap<HirId, Param>,
}

impl Func {
    fn params(&self) -> impl Iterator<Item = &Param> {
        self.index_map.values()
    }
}

#[derive(Debug)]
struct Return {
    span: Span,
    value: Option<Span>,
}

#[derive(Debug)]
struct Call {
    span: Span,
    callee: DefId,
    args: Vec<(Span, bool)>,
}

#[allow(unused)]
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
                let args = args
                    .iter()
                    .map(|arg| {
                        let is_null = as_int_lit(arg).map(|n| n == 0).unwrap_or(false);
                        (arg.span, is_null)
                    })
                    .collect();
                return Some(Call {
                    span,
                    callee: def_id,
                    args,
                });
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
    if let ExprKind::Lit(lit) = remove_cast_and_drop_temps(expr).kind {
        if let LitKind::Int(n, _) = lit.node {
            return Some(n);
        }
    }
    None
}

fn to_comma(span: Span, source_map: &SourceMap) -> Span {
    if source_map.span_look_ahead(span, ",", Some(1)).is_some() {
        span.with_hi(span.hi() + BytePos(1))
    } else {
        span
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
