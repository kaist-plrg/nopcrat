use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};

use etrace::some_or;
use rustc_ast::LitKind;
use rustc_hir::{
    def::Res, intravisit::Visitor as HVisitor, BinOpKind, Expr, ExprKind, FnRetTy, HirId, ItemKind,
    Node, PatKind, QPath, UnOp,
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
                    .unwrap();
                let ty = ty.strip_prefix("*mut ").expect(&ty).to_string();
                let param = Param {
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
        let mut remaining_return: Vec<_> = index_map.keys().copied().collect();
        let first_return = SuccValue::find(params);
        if let Some((_, first)) = &first_return {
            remaining_return.retain(|i| i != first);
        }
        let is_unit = matches!(sig.decl.output, FnRetTy::DefaultReturn(_));
        let func = Func {
            is_unit,
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
        let curr = funcs.get(&def_id);

        let mut ret_call_spans = BTreeSet::new();

        let mut visitor = BodyVisitor::new(tcx);
        visitor.visit_body(body);

        for call in visitor.calls {
            let Call {
                hir_id,
                span,
                callee,
                args,
            } = call;
            let func = some_or!(funcs.get(&callee), continue);

            for index in func.index_map.keys() {
                let span = to_comma(args[*index].span, source_map);
                fix(span, "".to_string());
            }

            let mut mtch = func.call_match(&args, curr);

            if let Some(call) = get_if_cmp_call(hir_id, span, tcx) {
                if let Some(then) = func.cmp(call.op, call.target) {
                    let if_span = call.if_span;
                    let if_span = if_span.with_hi(span.lo());
                    fix(if_span, "{ match ".to_string());

                    let succ = "Ok(v) => ";
                    let fail = "Err(_) => ";
                    let (_, i) = func.first_return.as_ref().unwrap();
                    let arg = &args[*i];
                    let assign = if arg.is_null {
                        "".to_string()
                    } else {
                        format!(" (*{}) = v;", arg.code)
                    };

                    let bt = if then { succ } else { fail };
                    let bt_span = call.then_span.shrink_to_lo().with_lo(span.hi());
                    fix(bt_span, format!(" {{\n{}", bt));

                    if then {
                        let pos = bt_span.hi() + BytePos(1);
                        let ba_span = bt_span.with_hi(pos).with_lo(pos);
                        fix(ba_span, assign.clone());
                    }

                    let be_span = call.then_span.shrink_to_hi();
                    if let Some(else_span) = call.else_span {
                        let be = if !then { succ } else { fail };
                        let be_span = be_span.with_hi(else_span.lo());
                        fix(be_span, format!("\n{}", be));

                        if !then {
                            let pos = be_span.lo() + BytePos(1);
                            let ba_span = be_span.with_hi(pos).with_lo(pos);
                            fix(ba_span, assign);
                        }

                        let pos = else_span.hi();
                        let end_span = else_span.with_hi(pos).with_lo(pos);
                        fix(end_span, "\n}}".to_string());
                    } else {
                        let (be, assign) = if !then {
                            (succ, assign)
                        } else {
                            (fail, "".to_string())
                        };
                        fix(be_span, format!("\n{} {{ {} }}\n}}}}", be, assign));
                    }

                    mtch = None
                }
            } else if let Some(expr) = get_parent(hir_id, tcx) {
                if matches!(expr.kind, ExprKind::Ret(_)) {
                    if let Some(func) = curr {
                        ret_call_spans.insert(expr.span);
                        let span = expr.span.with_hi(expr.span.lo() + BytePos(6));
                        fix(span, "let rv___ =".to_string());

                        let pos = expr.span.hi() + BytePos(1);
                        let span = expr.span.with_hi(pos).with_lo(pos);
                        let rv = func.return_value(Some("rv___".to_string()));
                        fix(span, format!("; return {};", rv));
                    }
                }
            }

            let mut binding = func.call_binding();
            if mtch.is_some() {
                binding = "match ".to_string() + &binding;
            }
            fix(span.shrink_to_lo(), binding);

            let mut assign = func.call_assign(&args, curr);
            if let Some(m) = &mtch {
                assign += m;
            }
            fix(span.shrink_to_hi(), assign);
        }

        let func = some_or!(curr, continue);
        for param in func.params() {
            fix(param.span, "".to_string());
        }

        let (span, orig) = match sig.decl.output {
            FnRetTy::Return(ty) => {
                let span = ty.span;
                let ty = source_map.span_to_snippet(span).unwrap();
                (span.with_lo(span.lo() - BytePos(3)), Some(ty))
            }
            FnRetTy::DefaultReturn(span) => (span, None),
        };
        let ret_ty = func.return_type(orig);
        fix(span, format!("-> {}", ret_ty));

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
            if ret_call_spans.contains(&span) {
                continue;
            }
            let orig = value.map(|value| source_map.span_to_snippet(value).unwrap());
            let ret_v = func.return_value(orig);
            fix(span, format!("return {}", ret_v));
        }

        if func.is_unit {
            let pos = body.value.span.hi() - BytePos(1);
            let span = body.value.span.with_lo(pos).with_hi(pos);
            let ret_v = func.return_value(None);
            fix(span, ret_v);
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
    must: bool,
    span: Span,
    hir_id: HirId,
    name: String,
    ty: String,
}

#[allow(unused)]
struct Func {
    is_unit: bool,
    first_return: Option<(SuccValue, usize)>,
    remaining_return: Vec<usize>,
    index_map: BTreeMap<usize, Param>,
    hir_id_map: BTreeMap<HirId, Param>,
}

impl Func {
    fn params(&self) -> impl Iterator<Item = &Param> {
        self.index_map.values()
    }

    fn cmp(&self, op: BinOpKind, target: u128) -> Option<bool> {
        let (sv, _) = &self.first_return?;
        let n = match *sv {
            SuccValue::Int(n) => n,
            SuccValue::Uint(n) => n as i128,
            _ => return None,
        };
        let m = target as i128;
        match op {
            BinOpKind::Eq => Some(n == m),
            BinOpKind::Ne => Some(n != m),
            BinOpKind::Lt => Some(n < m),
            BinOpKind::Le => Some(n <= m),
            BinOpKind::Gt => Some(n > m),
            BinOpKind::Ge => Some(n >= m),
            _ => None,
        }
    }

    fn call_binding(&self) -> String {
        let mut xs = vec![];
        if !self.is_unit {
            xs.push("rv___".to_string());
        }
        for i in &self.remaining_return {
            xs.push(format!("rv___{}", i));
        }
        if xs.len() == 1 {
            format!("{{ let {} = ", xs.pop().unwrap())
        } else {
            mk_string(xs.iter(), "{ let (", ", ", ") = ")
        }
    }

    fn is_must(curr: Option<&Self>, hir_id: &Option<HirId>) -> Option<bool> {
        let curr = curr?;
        let hir_id = hir_id.as_ref()?;
        let param = curr.hir_id_map.get(hir_id)?;
        Some(param.must)
    }

    fn call_assign(&self, args: &[Arg], curr: Option<&Self>) -> String {
        let mut assigns = vec![];
        for i in &self.remaining_return {
            let arg = &args[*i];
            if !arg.is_null {
                let param = &self.index_map[i];
                let need_some = !Self::is_must(curr, &arg.hir_id).unwrap_or(true);
                let assign = if need_some {
                    if param.must {
                        format!("{}___v = Some(rv___{});", arg.code, i)
                    } else {
                        format!(
                            "if let Some(v) = rv___{} {{ {}___v = Some(v); }}",
                            i, arg.code
                        )
                    }
                } else if param.must {
                    format!("*({}) = rv___{};", arg.code, i)
                } else {
                    format!("if let Some(v) = rv___{} {{ *({}) = v; }}", i, arg.code)
                };
                assigns.push(assign);
            }
        }
        mk_string(assigns.iter(), ";\n", "\n", "\nrv___ }")
    }

    fn call_match(&self, args: &[Arg], curr: Option<&Self>) -> Option<String> {
        let (succ_value, first) = &self.first_return?;
        let arg = &args[*first];
        let assign = if arg.is_null {
            "".to_string()
        } else {
            let need_some = !Self::is_must(curr, &arg.hir_id).unwrap_or(true);
            if need_some {
                format!("{}___v = Some(v);", arg.code)
            } else {
                format!("*({}) = v;", arg.code)
            }
        };
        let v = match succ_value {
            SuccValue::Int(v) => v.to_string(),
            SuccValue::Uint(v) => v.to_string(),
            SuccValue::Bool(v) => v.to_string(),
        };
        Some(format!(
            " {{\nOk(v) => {{ {} {} }}\nErr(v) => v,\n}}",
            assign, v
        ))
    }

    fn return_type(&self, orig: Option<String>) -> String {
        let mut tys = vec![];
        if let Some((_, i)) = &self.first_return {
            let orig = orig.unwrap();
            let param = &self.index_map[i];
            let ty = format!("Result<{}, {}>", param.ty, orig);
            tys.push(ty);
        } else if let Some(ty) = orig {
            tys.push(ty);
        }
        for i in &self.remaining_return {
            let param = &self.index_map[i];
            let ty = if param.must {
                param.ty.to_string()
            } else {
                format!("Option<{}>", param.ty)
            };
            tys.push(ty);
        }
        if tys.len() == 1 {
            tys.pop().unwrap()
        } else {
            mk_string(tys.iter(), "(", ", ", ")")
        }
    }

    fn return_value(&self, orig: Option<String>) -> String {
        let mut values = vec![];
        if let Some((_, i)) = &self.first_return {
            let orig = orig.unwrap();
            let param = &self.index_map[i];
            let v = format!("{}___v.ok_or({})", param.name, orig);
            values.push(v);
        } else if let Some(v) = orig {
            values.push(v);
        }
        for i in &self.remaining_return {
            let param = &self.index_map[i];
            let v = format!("{}___v", param.name);
            values.push(v);
        }
        if values.len() == 1 {
            values.pop().unwrap()
        } else {
            mk_string(values.iter(), "(", ", ", ")")
        }
    }
}

#[derive(Debug)]
struct Return {
    span: Span,
    value: Option<Span>,
}

#[derive(Debug)]
struct Call {
    hir_id: HirId,
    span: Span,
    callee: DefId,
    args: Vec<Arg>,
}

#[derive(Debug)]
struct Arg {
    span: Span,
    code: String,
    hir_id: Option<HirId>,
    is_null: bool,
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
    indirect_assigns: Vec<IndirectAssign>,
    null_checks: Vec<NullCheck>,
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
        match expr.kind {
            ExprKind::Ret(e) => {
                let span = expr.span;
                let value = e.as_ref().map(|e| e.span);
                self.returns.push(Return { span, value });
            }
            ExprKind::Call(callee, args) => {
                if let Some(path) = expr_to_path(callee) {
                    if let Res::Def(_, def_id) = path.res {
                        let source_map = self.tcx.sess.source_map();
                        let args = args
                            .iter()
                            .map(|arg| {
                                let code = source_map.span_to_snippet(arg.span).unwrap();
                                let hir_id = expr_to_path(arg).and_then(|path| {
                                    if let Res::Local(hir_id) = path.res {
                                        Some(hir_id)
                                    } else {
                                        None
                                    }
                                });
                                let is_null = as_int_lit(arg).map(|n| n == 0).unwrap_or(false);
                                Arg {
                                    span: arg.span,
                                    code,
                                    hir_id,
                                    is_null,
                                }
                            })
                            .collect();
                        let call = Call {
                            hir_id: expr.hir_id,
                            span: expr.span,
                            callee: def_id,
                            args,
                        };
                        self.calls.push(call);
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
    Int(i128),
    Uint(u128),
    Bool(bool),
}

impl SuccValue {
    fn from(rvs: &ReturnValues) -> Option<Self> {
        match rvs {
            ReturnValues::Int(succ, fail) => {
                let succ = succ.gamma()?;
                if succ.len() != 1 {
                    return None;
                }
                let fail = fail.gamma()?;
                if !succ.is_disjoint(fail) {
                    return None;
                }
                Some(Self::Int(*succ.first().unwrap()))
            }
            ReturnValues::Uint(succ, fail) => {
                let succ = succ.gamma()?;
                if succ.len() != 1 {
                    return None;
                }
                let fail = fail.gamma()?;
                if !succ.is_disjoint(fail) {
                    return None;
                }
                Some(Self::Uint(*succ.first().unwrap()))
            }
            ReturnValues::Bool(succ, fail) => {
                let succ = succ.gamma();
                if succ.len() != 1 {
                    return None;
                }
                let succ = succ.first().unwrap();
                let fail = fail.gamma();
                if fail.len() != 1 {
                    return None;
                }
                let fail = fail.first().unwrap();
                if succ == fail {
                    return None;
                }
                Some(Self::Bool(*succ))
            }
            _ => None,
        }
    }

    fn find(params: &[OutputParam]) -> Option<(Self, usize)> {
        params.iter().find_map(|param| {
            if !param.must {
                Some((Self::from(&param.return_values)?, param.index))
            } else {
                None
            }
        })
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

fn get_parent(hir_id: HirId, tcx: TyCtxt<'_>) -> Option<&Expr<'_>> {
    let hir = tcx.hir();
    let Node::Expr(e) = hir.find_parent(hir_id)? else {
        return None;
    };
    match e.kind {
        ExprKind::DropTemps(_) | ExprKind::Cast(_, _) => get_parent(e.hir_id, tcx),
        _ => Some(e),
    }
}

#[derive(Debug)]
struct IfCmpCall {
    if_span: Span,
    target: u128,
    op: BinOpKind,
    then_span: Span,
    else_span: Option<Span>,
}

fn get_if_cmp_call(hir_id: HirId, span: Span, tcx: TyCtxt<'_>) -> Option<IfCmpCall> {
    let pexpr = get_parent(hir_id, tcx)?;
    let ExprKind::Binary(op, lhs, rhs) = pexpr.kind else {
        return None;
    };
    let ppexpr = get_parent(pexpr.hir_id, tcx)?;
    let ExprKind::If(c, t, f) = ppexpr.kind else {
        return None;
    };
    if !c.span.overlaps(pexpr.span) {
        return None;
    }
    let target = if lhs.span.overlaps(span) { rhs } else { lhs };
    let call = IfCmpCall {
        if_span: ppexpr.span,
        target: as_int_lit(target)?,
        op: op.node,
        then_span: t.span,
        else_span: f.map(|f| f.span),
    };
    Some(call)
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
