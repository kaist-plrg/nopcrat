use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};

use etrace::some_or;
use rustc_ast::LitKind;
use rustc_hir::{
    def::Res, intravisit::Visitor as HVisitor, BinOp, BinOpKind, Expr, ExprKind, FnRetTy, HirId,
    ItemKind, MutTy, Node, PatKind, PathSegment, QPath, TyKind,
};
use rustc_middle::{
    hir::nested_filter,
    mir::{BasicBlock, TerminatorKind},
    ty::TyCtxt,
};
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

    let mut def_id_ty_map = BTreeMap::new();
    for id in hir.items() {
        let item = hir.item(id);
        let ItemKind::TyAlias(ty, _) = item.kind else {
            continue;
        };
        let TyKind::Ptr(MutTy { ty, .. }) = ty.kind else {
            continue;
        };
        let def_id = item.owner_id.to_def_id();
        let ty = source_map.span_to_snippet(ty.span).unwrap();
        def_id_ty_map.insert(def_id, ty);
    }

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
        let mir_body = tcx.optimized_mir(def_id);
        let index_map: BTreeMap<_, _> = params
            .iter()
            .map(|param| {
                let OutputParam {
                    index,
                    must,
                    complete_writes,
                    ..
                } = param;
                let param = &body.params[*index];

                let assign_writes: Vec<_> = complete_writes
                    .iter()
                    .filter_map(|cw| {
                        let CompleteWrite {
                            block: bb,
                            statement_index: i,
                            ..
                        } = cw;
                        let bbd = &mir_body.basic_blocks[BasicBlock::from_usize(*bb)];
                        if *i != bbd.statements.len() {
                            Some(bbd.statements[*i].source_info.span)
                        } else {
                            None
                        }
                    })
                    .collect();
                let write_args: BTreeMap<_, _> = complete_writes
                    .iter()
                    .filter_map(|cw| {
                        let CompleteWrite {
                            block: bb,
                            statement_index: i,
                            write_arg,
                        } = cw;
                        let bbd = &mir_body.basic_blocks[BasicBlock::from_usize(*bb)];
                        if *i == bbd.statements.len() {
                            let t = bbd.terminator();
                            assert!(matches!(t.kind, TerminatorKind::Call { .. }), "{:?}", t);
                            let span = t.source_info.span;
                            write_arg.as_ref().map(|arg| (span, *arg))
                        } else {
                            None
                        }
                    })
                    .collect();
                let PatKind::Binding(_, hir_id, ident, _) = param.pat.kind else {
                    unreachable!()
                };
                let span = to_comma(param.span, source_map);
                let name = ident.name.to_ident_string();
                let ty = &sig.decl.inputs[*index];
                let ty = match ty.kind {
                    TyKind::Ptr(MutTy { ty, .. }) => source_map.span_to_snippet(ty.span).unwrap(),
                    TyKind::Path(QPath::Resolved(_, path)) => {
                        let Res::Def(_, def_id) = path.res else {
                            unreachable!("{:?}", ty);
                        };
                        def_id_ty_map
                            .get(&def_id)
                            .expect(&format!("{:?}", ty))
                            .clone()
                    }
                    _ => unreachable!("{:?}", ty),
                };
                let param = Param {
                    must: *must,
                    assign_writes,
                    write_args,
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

            let assign_map = curr.map(|c| c.assign_map(span)).unwrap_or_default();
            let mut mtch = func.call_match(&args, &assign_map);

            if let Some(call) = get_if_cmp_call(hir_id, span, tcx) {
                if let Some(then) = func.cmp(call.op, call.target) {
                    let if_span = call.if_span;
                    let if_span = if_span.with_hi(span.lo());
                    fix(if_span, "{ match ".to_string());

                    let succ = "Ok(v) => ";
                    let fail = "Err(_) => ";
                    let (_, i) = func.first_return.as_ref().unwrap();
                    let arg = &args[*i];
                    let set_flag = if let Some(arg) = assign_map.get(i) {
                        format!("{}___s = true;", arg)
                    } else {
                        "".to_string()
                    };
                    let assign = if arg.code.contains("&mut ") {
                        format!(" *({}) = v; {}", arg.code, set_flag)
                    } else {
                        format!(
                            " if !({0}).is_null() {{ *({0}) = v; {1} }}",
                            arg.code, set_flag
                        )
                    };

                    let bt = if then { succ } else { fail };
                    let bt_span = call.then_span.shrink_to_lo().with_lo(span.hi());
                    fix(bt_span, format!(" {{ {}", bt));

                    if then {
                        let pos = bt_span.hi() + BytePos(1);
                        let ba_span = bt_span.with_hi(pos).with_lo(pos);
                        fix(ba_span, assign.clone());
                    }

                    let be_span = call.then_span.shrink_to_hi();
                    if let Some(else_span) = call.else_span {
                        let be = if !then { succ } else { fail };
                        let be_span = be_span.with_hi(else_span.lo());
                        fix(be_span, format!(" {}", be));

                        if !then {
                            let pos = be_span.hi() + BytePos(1);
                            let ba_span = be_span.with_hi(pos).with_lo(pos);
                            fix(ba_span, assign);
                        }

                        let pos = else_span.hi();
                        let end_span = else_span.with_hi(pos).with_lo(pos);
                        fix(end_span, " }}".to_string());
                    } else {
                        let (be, assign) = if !then {
                            (succ, assign)
                        } else {
                            (fail, "".to_string())
                        };
                        fix(be_span, format!(" {} {{ {} }} }}}}", be, assign));
                    }

                    mtch = None
                }
            } else if let Some(expr) = get_parent_return(hir_id, tcx) {
                if let Some(func) = curr {
                    ret_call_spans.insert(expr.span);
                    let pre_span = expr.span.with_hi(span.lo());
                    fix(pre_span, "let rv___ =".to_string());

                    let pre_span = pre_span.with_lo(pre_span.lo() + BytePos(6));
                    let pre_s = source_map.span_to_snippet(pre_span).unwrap();

                    let post_span = expr.span.with_lo(span.hi());
                    let post_s = source_map.span_to_snippet(post_span).unwrap();

                    let post_span = post_span.with_hi(post_span.hi() + BytePos(1));
                    let rv = format!("{}rv___{}", pre_s, post_s);
                    let rv = func.return_value(Some(rv));
                    fix(post_span, format!("; return {};", rv));
                }
            }

            let mut binding = func.call_binding();
            if mtch.is_some() {
                binding = "(match ".to_string() + &binding;
            }
            fix(span.shrink_to_lo(), binding);

            let mut assign = func.call_assign(&args, &assign_map);
            if let Some(m) = &mtch {
                assign += m;
                assign += ")";
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
    let mut {0}___s: bool = false;
    let mut {0}___v: {1} = std::mem::transmute([0u8; std::mem::size_of::<{1}>()]);
    let mut {0}: *mut {1} = &mut {0}___v;",
                        param.name, param.ty,
                    )
                }
            })
            .collect();

        let pos = body.value.span.lo() + BytePos(1);
        let span = body.value.span.with_lo(pos).with_hi(pos);
        fix(span, local_vars);

        for param in func.params() {
            for span in &param.assign_writes {
                let pos = span.hi() + BytePos(1);
                let span = span.with_hi(pos).with_lo(pos);
                let assign = format!("{0}___s = true;", param.name);
                fix(span, assign);
            }
        }

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

        for check in visitor.null_checks {
            let NullCheck {
                span,
                hir_id,
                value,
            } = check;
            if !func.hir_id_map.contains_key(&hir_id) {
                continue;
            }
            fix(span, value.to_string());
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
    assign_writes: Vec<Span>,
    write_args: BTreeMap<Span, usize>,
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
            format!("({{ let {} = ", xs.pop().unwrap())
        } else {
            mk_string(xs.iter(), "({ let (", ", ", ") = ")
        }
    }

    fn assign_map(&self, span: Span) -> BTreeMap<usize, String> {
        let mut map = BTreeMap::new();
        for p in self.params() {
            let arg_idx = *some_or!(p.write_args.get(&span), continue);
            map.insert(arg_idx, p.name.clone());
        }
        map
    }

    fn call_assign(&self, args: &[Arg], assign_map: &BTreeMap<usize, String>) -> String {
        let mut assigns = vec![];
        for i in &self.remaining_return {
            let arg = &args[*i];
            let param = &self.index_map[i];
            let set_flag = if let Some(arg) = assign_map.get(i) {
                format!("{}___s = true;", arg)
            } else {
                "".to_string()
            };
            let assign = if param.must {
                if arg.code.contains("&mut ") {
                    format!("*({}) = rv___{}; {}", arg.code, i, set_flag)
                } else {
                    format!(
                        "if !({0}).is_null() {{ *({0}) = rv___{1}; {2} }}",
                        arg.code, i, set_flag
                    )
                }
            } else if arg.code.contains("&mut ") {
                format!(
                    "if let Some(v) = rv___{} {{ *({}) = v; {} }}",
                    i, arg.code, set_flag
                )
            } else {
                format!(
                    "if !({0}).is_null() {{ if let Some(v) = rv___{1} {{ *({0}) = v; {2} }} }}",
                    arg.code, i, set_flag
                )
            };
            assigns.push(assign);
        }
        let end = if self.is_unit { " })" } else { " rv___ })" };
        mk_string(assigns.iter(), "; ", " ", end)
    }

    fn call_match(&self, args: &[Arg], assign_map: &BTreeMap<usize, String>) -> Option<String> {
        let (succ_value, first) = &self.first_return?;
        let arg = &args[*first];
        let set_flag = if let Some(arg) = assign_map.get(first) {
            format!("{}___s = true;", arg)
        } else {
            "".to_string()
        };
        let assign = if arg.code.contains("&mut ") {
            format!("*({}) = v; {}", arg.code, set_flag)
        } else {
            format!(
                "if !({0}).is_null() {{ *({0}) = v; {1} }}",
                arg.code, set_flag
            )
        };
        let v = match succ_value {
            SuccValue::Int(v) => v.to_string(),
            SuccValue::Uint(v) => v.to_string(),
            SuccValue::Bool(v) => v.to_string(),
        };
        Some(format!(
            " {{ Ok(v) => {{ {} {} }} Err(v) => v, }}",
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
            let v = format!(
                "if {0}___s {{ Ok({0}___v) }} else {{ Err({1}) }}",
                param.name, orig
            );
            values.push(v);
        } else if let Some(v) = orig {
            values.push(v);
        }
        for i in &self.remaining_return {
            let param = &self.index_map[i];
            let v = if param.must {
                format!("{}___v", param.name)
            } else {
                format!("if {0}___s {{ Some({0}___v) }} else {{ None }}", param.name)
            };
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
}

#[derive(Debug)]
struct NullCheck {
    span: Span,
    hir_id: HirId,
    value: bool,
}

struct BodyVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    returns: Vec<Return>,
    calls: Vec<Call>,
    null_checks: Vec<NullCheck>,
}

impl<'tcx> BodyVisitor<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            returns: vec![],
            calls: vec![],
            null_checks: vec![],
        }
    }
}

impl<'tcx> BodyVisitor<'tcx> {
    fn visit_expr_ret(&mut self, expr: &'tcx Expr<'tcx>, e: Option<&'tcx Expr<'tcx>>) {
        let value = e.as_ref().map(|e| e.span);
        let ret = Return {
            span: expr.span,
            value,
        };
        self.returns.push(ret);
    }

    fn visit_expr_call(
        &mut self,
        expr: &'tcx Expr<'tcx>,
        callee: &'tcx Expr<'tcx>,
        args: &'tcx [Expr<'tcx>],
    ) {
        let path = some_or!(expr_to_path(callee), return);
        let Res::Def(_, def_id) = path.res else {
            return;
        };
        if !def_id.is_local() {
            return;
        }
        let source_map = self.tcx.sess.source_map();
        let args = args
            .iter()
            .map(|arg| {
                let code = source_map.span_to_snippet(arg.span).unwrap();
                Arg {
                    span: arg.span,
                    code,
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

    fn visit_expr_binary(
        &mut self,
        expr: &'tcx Expr<'tcx>,
        op: BinOp,
        l: &'tcx Expr<'tcx>,
        r: &'tcx Expr<'tcx>,
    ) {
        let value = match op.node {
            BinOpKind::Eq => false,
            BinOpKind::Ne => true,
            _ => return,
        };
        let l = remove_cast(l);
        let r = remove_cast(r);
        let (x, n) = if let (Some(x), Some(n)) = (expr_to_path(l), as_int_lit(r)) {
            (x, n)
        } else if let (Some(x), Some(n)) = (expr_to_path(r), as_int_lit(l)) {
            (x, n)
        } else {
            return;
        };
        if n != 0 {
            return;
        }
        let Res::Local(hir_id) = x.res else { return };
        let check = NullCheck {
            span: expr.span,
            hir_id,
            value,
        };
        self.null_checks.push(check);
    }

    fn visit_expr_method_call(
        &mut self,
        expr: &'tcx Expr<'tcx>,
        seg: &'tcx PathSegment<'tcx>,
        receiver: &'tcx Expr<'tcx>,
        _: &'tcx [Expr<'tcx>],
        _: Span,
    ) {
        if seg.ident.name.to_ident_string() != "is_null" {
            return;
        }
        let path = some_or!(expr_to_path(receiver), return);
        let Res::Local(hir_id) = path.res else { return };
        let check = NullCheck {
            span: expr.span,
            hir_id,
            value: false,
        };
        self.null_checks.push(check);
    }
}

impl<'tcx> HVisitor<'tcx> for BodyVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.tcx.hir()
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        match expr.kind {
            ExprKind::Ret(e) => self.visit_expr_ret(expr, e),
            ExprKind::Call(callee, args) => self.visit_expr_call(expr, callee, args),
            ExprKind::Binary(op, l, r) => self.visit_expr_binary(expr, op, l, r),
            ExprKind::MethodCall(seg, receiver, args, span) => {
                self.visit_expr_method_call(expr, seg, receiver, args, span)
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

fn remove_cast<'a, 'tcx>(expr: &'a Expr<'tcx>) -> &'a Expr<'tcx> {
    if let ExprKind::Cast(expr, _) | ExprKind::DropTemps(expr) = expr.kind {
        remove_cast(expr)
    } else {
        expr
    }
}

fn as_int_lit(expr: &Expr<'_>) -> Option<u128> {
    if let ExprKind::Lit(lit) = remove_cast(expr).kind {
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

fn get_parent_return(hir_id: HirId, tcx: TyCtxt<'_>) -> Option<&Expr<'_>> {
    let parent = get_parent(hir_id, tcx)?;
    if let ExprKind::Ret(_) = parent.kind {
        Some(parent)
    } else {
        get_parent_return(parent.hir_id, tcx)
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
    let code = tcx.sess.source_map().span_to_snippet(ppexpr.span).unwrap();
    if !code.starts_with("if") {
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
