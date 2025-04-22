use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};

use etrace::some_or;
use rustc_ast::LitKind;
use rustc_hash::FxHashMap;
use rustc_hir::{
    def::Res, intravisit::Visitor as HVisitor, BinOpKind, Expr, ExprKind, FnRetTy, HirId, ItemKind,
    MutTy, Node, PatKind, QPath, TyKind, UnOp,
};
use rustc_middle::{
    hir::nested_filter,
    mir::{BasicBlock, TerminatorKind},
    ty::TyCtxt,
};
use rustc_span::{def_id::DefId, source_map::SourceMap, BytePos, Span};
use rustfix::Suggestion;

use crate::{ai::analysis::*, compile_util};

#[derive(Default, Clone, Copy)]
struct Counter {
    simplify: bool,
    removed_value_defs: usize,
    removed_pointer_defs: usize,
    removed_pointer_uses: usize,
    direct_returns: usize,
    success_returns: usize,
    failure_returns: usize,
    removed_flag_sets: usize,
    removed_flag_defs: usize,
}

pub fn transform_path(path: &Path, analysis_result: &AnalysisResult, simplify: bool) {
    let input = compile_util::path_to_input(path);
    let config = compile_util::make_config(input);
    let suggestions =
        compile_util::run_compiler(config, |tcx| transform(tcx, analysis_result, simplify))
            .unwrap();
    compile_util::apply_suggestions(&suggestions);
}

fn transform(
    tcx: TyCtxt<'_>,
    analysis_result: &AnalysisResult,
    simplify: bool,
) -> BTreeMap<PathBuf, Vec<Suggestion>> {
    let mut counter = Counter {
        simplify,
        ..Counter::default()
    };

    let source_map = tcx.sess.source_map();

    let mut def_id_ty_map = FxHashMap::default();
    for id in tcx.hir_free_items() {
        let item = tcx.hir_item(id);
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

    let mut funcs = FxHashMap::default();
    let mut rcfws = FxHashMap::default();
    let mut wbrs = FxHashMap::default();
    for id in tcx.hir_free_items() {
        let item = tcx.hir_item(id);
        let ItemKind::Fn { sig, body, .. } = item.kind else {
            continue;
        };
        let def_id = id.owner_id.to_def_id();
        let name = tcx.def_path_str(def_id);
        let fn_analysis_result = some_or!(analysis_result.get(&name), continue);
        let body = tcx.hir_body(body);
        let mir_body = tcx.optimized_mir(def_id);
        let index_map: BTreeMap<_, _> = fn_analysis_result
            .output_params
            .iter()
            .map(|param| {
                let OutputParam {
                    index,
                    must,
                    complete_writes,
                    ..
                } = param;
                let param = &body.params[*index];

                let writes: Vec<_> = complete_writes
                    .iter()
                    .map(|cw| {
                        let CompleteWrite {
                            block: bb,
                            statement_index: i,
                            ..
                        } = cw;
                        let bbd = &mir_body.basic_blocks[BasicBlock::from_usize(*bb)];
                        if *i != bbd.statements.len() {
                            bbd.statements[*i].source_info.span
                        } else {
                            bbd.terminator().source_info.span
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
                            .unwrap_or_else(|| panic!("{:?}", ty))
                            .clone()
                    }
                    _ => unreachable!("{:?}", ty),
                };
                let param = Param {
                    must: *must,
                    writes,
                    write_args,
                    name,
                    ty,
                    span,
                    hir_id,
                };
                (*index, param)
            })
            .collect();

        wbrs.insert(
            def_id,
            fn_analysis_result
                .wbrs
                .iter()
                .map(|wbr| {
                    (
                        wbr.span.to_span(),
                        (
                            wbr.mays
                                .iter()
                                .filter_map(|i| index_map.get(i).map(|p| p.name.clone()))
                                .collect::<Vec<_>>(),
                            wbr.musts
                                .iter()
                                .filter_map(|i| index_map.get(i).map(|p| p.name.clone()))
                                .collect::<Vec<_>>(),
                        ),
                    )
                })
                .collect::<Vec<_>>(),
        );

        rcfws.insert(
            def_id,
            fn_analysis_result
                .rcfws
                .iter()
                .map(|(index, spans)| {
                    (
                        index_map.get(index).cloned().unwrap().name,
                        spans.iter().map(|sp| sp.to_span()).collect(),
                    )
                })
                .collect::<BTreeMap<String, Vec<Span>>>(),
        );

        let hir_id_map: BTreeMap<_, _> = index_map
            .values()
            .cloned()
            .map(|param| (param.hir_id, param))
            .collect();
        let mut remaining_return: Vec<_> = index_map.keys().copied().collect();
        let first_return = SuccValue::find(&fn_analysis_result.output_params);
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
    for id in tcx.hir_free_items() {
        let item = tcx.hir_item(id);
        let ItemKind::Fn { sig, body, .. } = item.kind else {
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
        let body = tcx.hir_body(body);
        let curr = funcs.get(&def_id);

        let default = BTreeMap::new();
        let rcfw = rcfws.get(&def_id).unwrap_or(&default);

        let mut visitor = BodyVisitor::new(tcx);
        visitor.visit_body(body);

        let passes = BTreeSet::from_iter(visitor.passes.iter());

        let mut ret_call_spans = BTreeSet::new();
        let mut call_spans = BTreeSet::new();

        // in deref expression, pointer name to expression span
        let mut ref_to_spans: BTreeMap<String, Vec<Span>> = BTreeMap::new();

        // in deref expression in return, return span to pointer name and deref span
        let mut ret_to_ref_spans: BTreeMap<Span, Vec<(String, Span)>> = BTreeMap::new();

        // in deref expression in call, pointer name and deref span
        let mut ref_and_call_spans = vec![];

        // name of pointers in the return or call
        let mut ref_call_or_ret = BTreeSet::new();

        if simplify {
            if let Some(func) = curr {
                let hirids = BTreeSet::from_iter(
                    visitor
                        .calls
                        .iter()
                        .filter_map(|c| funcs.get(&c.callee).map(|_| c.hir_id)),
                );
                let params = BTreeSet::from_iter(func.params().map(|p| p.name.clone()));

                for rf in visitor.refs {
                    let Ref { hir_id, span, name } = rf;
                    if params.contains(&name) && !passes.contains(&name) {
                        if let Some(expr) = get_parent_call(hir_id, tcx) {
                            if hirids.contains(&expr.hir_id) {
                                ref_call_or_ret.insert(name.clone());
                                ref_and_call_spans.push((name, span));
                                continue;
                            }
                        }

                        if let Some(expr) = get_parent_return(hir_id, tcx) {
                            ref_call_or_ret.insert(name.clone());
                            ret_to_ref_spans
                                .entry(expr.span)
                                .or_default()
                                .push((name, span));
                            continue;
                        }

                        ref_to_spans.entry(name.clone()).or_default().push(span);
                    }
                }
            }
        }

        for call in visitor.calls.clone() {
            let Call {
                hir_id,
                span,
                callee,
                args,
            } = call;
            let func = some_or!(funcs.get(&callee), continue);
            call_spans.insert(span);

            let mut args = args.clone();

            if simplify {
                for arg in args.iter_mut() {
                    for (name, span) in &ref_and_call_spans {
                        if arg.span.contains(*span) {
                            let pre_span = arg.span.with_hi(span.lo());
                            let post_span = arg.span.with_lo(span.hi());

                            let pre_s = source_map.span_to_snippet(pre_span).unwrap();
                            let post_s = source_map.span_to_snippet(post_span).unwrap();

                            arg.code = format!("{}{}___v{}", pre_s, name, post_s);
                            counter.removed_pointer_uses += 1;
                        }
                    }
                }
            }

            for index in func.index_map.keys() {
                let span = to_comma(args[*index].span, source_map);
                fix(span, "".to_string());
            }

            let assign_map = curr.map(|c| c.assign_map(span)).unwrap_or_default();

            let mut mtch = func.first_return.and_then(|(_, first)| {
                let set_flag = generate_set_flag(&span, &first, rcfw, &assign_map, &mut counter);
                func.call_match(&args, set_flag)
            });

            if let Some(call) = get_if_cmp_call(hir_id, span, tcx) {
                if let Some(then) = func.cmp(call.op, call.target) {
                    let if_span = call.if_span;
                    let if_span = if_span.with_hi(span.lo());
                    fix(if_span, "{ match ".to_string());

                    let succ = "Ok(v___) => ";
                    let fail = "Err(_) => ";
                    let (_, i) = func.first_return.as_ref().unwrap();
                    let arg = &args[*i];
                    let set_flag = generate_set_flag(&span, i, rcfw, &assign_map, &mut counter);
                    let assign = if arg.code.contains("&mut ") {
                        format!(" *({}) = v___; {}", arg.code, set_flag)
                    } else {
                        format!(
                            " if !({0}).is_null() {{ *({0}) = v___; {1} }}",
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
                        fix(be_span, format!(" {} {{", be));

                        if !then {
                            let pos = be_span.hi();
                            let ba_span = be_span.with_hi(pos).with_lo(pos);
                            fix(ba_span, assign);
                        }

                        let pos = else_span.hi();
                        let end_span = else_span.with_hi(pos).with_lo(pos);
                        // close1
                        fix(end_span, " }}}".to_string());
                    } else {
                        let (be, assign) = if !then {
                            (succ, assign)
                        } else {
                            (fail, "".to_string())
                        };
                        // close2
                        fix(be_span, format!(" {} {{ {} }} }}}}", be, assign));
                    }

                    mtch = None
                }
            } else if let Some(expr) = get_parent_return(hir_id, tcx) {
                if let Some(func) = curr {
                    let arm = matches!(tcx.parent_hir_node(expr.hir_id), Node::Arm(_));
                    ret_call_spans.insert(expr.span);
                    let pre_span = expr.span.with_hi(span.lo());
                    fix(
                        pre_span,
                        format!("{}let mut rv___ =", if arm { "{ " } else { "" }),
                    );

                    let pre_span = pre_span.with_lo(pre_span.lo() + BytePos(6));
                    let pre_s = source_map.span_to_snippet(pre_span).unwrap();

                    let post_span = expr.span.with_lo(span.hi());
                    let post_s = source_map.span_to_snippet(post_span).unwrap();

                    let post_span = post_span.with_hi(post_span.hi() + BytePos(1));
                    let rv = format!("{}rv___{}", pre_s, post_s);
                    let rv = func.return_value(
                        Some(rv),
                        wbrs[&def_id]
                            .iter()
                            .find(|(sp, _)| span.contains(*sp))
                            .map(|r| &r.1),
                        None,
                        &mut counter,
                    );
                    fix(
                        post_span,
                        format!("; return {};{}", rv, if arm { " }" } else { "" }),
                    );
                }
            }

            let mut binding = func.call_binding();
            if mtch.is_some() {
                binding = "(match ".to_string() + &binding;
            }
            fix(span.shrink_to_lo(), binding);

            let set_flags = func
                .remaining_return
                .iter()
                .map(|i| {
                    (
                        *i,
                        generate_set_flag(&span, i, rcfw, &assign_map, &mut counter),
                    )
                })
                .collect();

            let mut assign = func.call_assign(&args, &set_flags);
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

        let mut flag_unsimplifiable = BTreeSet::new();
        for param in func.params() {
            let rcfw = rcfw.get(&param.name);

            for span in &param.writes {
                if let Some(rcfw) = rcfw {
                    if rcfw.iter().any(|sp| span.contains(*sp)) && simplify {
                        counter.removed_flag_sets += 1;
                        continue;
                    }
                }

                flag_unsimplifiable.insert(&param.name);

                if call_spans.contains(span) {
                    continue;
                }

                let pos = span.hi() + BytePos(1);
                let span = span.with_hi(pos).with_lo(pos);
                let assign = format!("{0}___s = true;", param.name);
                fix(span, assign);
            }
        }

        for ret in visitor.returns.iter() {
            let Return { span, value } = ret;
            if ret_call_spans.contains(span) || ret_to_ref_spans.contains_key(span) {
                continue;
            }

            let orig = value.map(|value| source_map.span_to_snippet(value).unwrap());
            let mut lit_map = None;

            if simplify {
                let mut assign_before_ret = None;

                for assign in visitor.assigns.iter() {
                    if visitor
                        .calls
                        .iter()
                        .any(|call| call.span.overlaps(assign.span))
                    {
                        continue;
                    }
                    if source_map
                        .span_to_snippet(assign.span.between(*span))
                        .unwrap()
                        .chars()
                        .all(|c| c.is_whitespace())
                    {
                        assign_before_ret = Some(assign);
                        break;
                    }
                }

                if let Some(assign_before_ret) = assign_before_ret {
                    let Assign {
                        name,
                        value,
                        span: sp,
                    } = assign_before_ret;

                    if let Some(spans) = ref_to_spans.get_mut(name) {
                        spans.retain(|span| !sp.contains(*span));
                        lit_map = Some((name, value));
                        fix(*sp, "".to_string());
                    }
                }
            }

            let ret_v = func.return_value(
                orig,
                wbrs[&def_id]
                    .iter()
                    .find(|(sp, _)| span.contains(*sp))
                    .map(|r| &r.1),
                lit_map,
                &mut counter,
            );
            fix(*span, format!("return {}", ret_v));
        }

        let mut value_simplifiable = BTreeSet::new();

        if simplify {
            for param in func.params() {
                if passes.contains(&param.name) {
                    continue;
                }

                if let Some(spans) = ref_to_spans.get(&param.name) {
                    if spans.is_empty() && !ref_call_or_ret.contains(&param.name) {
                        value_simplifiable.insert(param.name.clone());
                        continue;
                    }
                    for span in spans {
                        let assign = format!("{}___v", param.name);
                        counter.removed_pointer_uses += 1;
                        fix(*span, assign);
                    }
                }
            }

            for (span, mut ss) in ret_to_ref_spans {
                let mut post_spans = vec![];

                ss.sort_by_key(|x| x.1);

                let s = ss[0].1;

                let pre_span = span.with_hi(s.lo()).with_lo(span.lo() + BytePos(6));
                post_spans.push(span.with_lo(s.hi()));

                for (i, (_, s)) in ss[1..].iter().enumerate() {
                    post_spans[i] = post_spans[i].with_hi(s.lo());
                    post_spans.push(span.with_lo(s.hi()));
                }

                let pre_s = source_map.span_to_snippet(pre_span).unwrap();
                let post_s = source_map.span_to_snippet(post_spans[0]).unwrap();

                let mut rv = format!("{}{}___v{}", pre_s, ss[0].0, post_s);
                counter.removed_pointer_uses += 1;

                for (i, s) in post_spans[1..].iter().enumerate() {
                    let post_s = source_map.span_to_snippet(*s).unwrap();
                    rv.push_str(&ss[i + 1].0);
                    rv.push_str("___v");
                    rv.push_str(&post_s);
                    counter.removed_pointer_uses += 1;
                }
                let rv = func.return_value(
                    Some(rv),
                    wbrs[&def_id]
                        .iter()
                        .find(|(sp, _)| span.contains(*sp))
                        .map(|r| &r.1),
                    None,
                    &mut counter,
                );

                fix(span, format!("return {}", rv));
            }
        }

        // Add definitions of additional local variables
        let local_vars: String = func
            .params()
            .map(|param| {
                let mut defs = String::from("\n    ");
                let value_decl = format!("let mut {0}___v: {1} = std::mem::transmute([0u8; std::mem::size_of::<{1}>()]);", param.name, param.ty);
                let ref_decl = format!("let mut {0}: *mut {1} = &mut {0}___v;", param.name, param.ty);
                let flag_decl = format!("let mut {}___s: bool = false;", param.name);

                // Decide whether add the flag or not
                if !param.must {
                    if flag_unsimplifiable.contains(&param.name) || !simplify {
                        defs.push_str(&flag_decl);
                        defs.push(' ');
                    } else {
                        counter.removed_flag_defs += 1;
                    }
                }

                // Decide whether add the value and the reference
                if passes.contains(&param.name) || !simplify {
                    defs.push_str(&value_decl);
                    defs.push(' ');
                    defs.push_str(&ref_decl);
                } else if value_simplifiable.contains(&param.name) {
                    counter.removed_value_defs += 1;
                    counter.removed_pointer_defs += 1;
                    defs = String::new();
                } else {
                    counter.removed_pointer_defs += 1;
                    defs.push_str(&value_decl);
                }

                defs
            })
            .collect();

        let pos = body.value.span.lo() + BytePos(1);
        let span = body.value.span.with_lo(pos).with_hi(pos);
        fix(span, local_vars);

        if func.is_unit {
            let pos = body.value.span.hi() - BytePos(1);
            let span = body.value.span.with_lo(pos).with_hi(pos);
            let pos = pos - BytePos(3);
            let prev = span.with_lo(pos).with_hi(pos);

            let mut skip = false;

            for ret in visitor.returns {
                let Return { span, value: _ } = ret;
                if span.overlaps(prev) {
                    skip = true;
                    break;
                }
            }

            if !skip {
                let ret_v = func.return_value(None, None, None, &mut counter);
                fix(span, format!("\t{}\n", ret_v));
            }
        }
    }
    suggestions.retain(|_, v| !v.is_empty());
    for suggestions in suggestions.values_mut() {
        suggestions.sort_by_key(|s| {
            (
                s.snippets[0].range.start,
                // close2 precedes close1
                usize::MAX - s.solutions[0].replacements[0].replacement.len(),
            )
        });
    }

    if simplify {
        println!("Removed value defs: {}", counter.removed_value_defs);
        println!("Removed pointer defs: {}", counter.removed_pointer_defs);
        println!("Removed pointer uses: {}", counter.removed_pointer_uses);
        println!("Direct returns: {}", counter.direct_returns);
        println!("Success returns: {}", counter.success_returns);
        println!("Failure returns: {}", counter.failure_returns);
        println!("Removed flag sets: {}", counter.removed_flag_sets);
        println!("Removed flag defs: {}", counter.removed_flag_defs);
    }

    suggestions
}

#[derive(Debug, Clone)]
struct Param {
    must: bool,
    writes: Vec<Span>,
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

    fn call_assign(&self, args: &[Arg], set_flags: &BTreeMap<usize, String>) -> String {
        let mut assigns = vec![];
        for i in &self.remaining_return {
            let arg = &args[*i];
            let param = &self.index_map[i];
            let assign = if param.must {
                if arg.code.contains("&mut ") {
                    format!("*({}) = rv___{}; {}", arg.code, i, set_flags[i])
                } else {
                    format!(
                        "if !({0}).is_null() {{ *({0}) = rv___{1}; {2} }}",
                        arg.code, i, set_flags[i]
                    )
                }
            } else if arg.code.contains("&mut ") {
                format!(
                    "if let Some(v___) = rv___{} {{ *({}) = v___; {} }}",
                    i, arg.code, set_flags[i]
                )
            } else {
                format!(
                    "if !({0}).is_null() {{ if let Some(v___) = rv___{1} {{ *({0}) = v___; {2} }} }}",
                    arg.code, i, set_flags[i]
                )
            };
            assigns.push(assign);
        }
        let end = if self.is_unit { " })" } else { " rv___ })" };
        mk_string(assigns.iter(), "; ", " ", end)
    }

    fn call_match(&self, args: &[Arg], set_flag: String) -> Option<String> {
        let (succ_value, first) = &self.first_return?;
        let arg = &args[*first];
        let assign = if arg.code.contains("&mut ") {
            format!("*({}) = v___; {}", arg.code, set_flag)
        } else {
            format!(
                "if !({0}).is_null() {{ *({0}) = v___; {1} }}",
                arg.code, set_flag
            )
        };
        let v = match succ_value {
            SuccValue::Int(v) => v.to_string(),
            SuccValue::Uint(v) => v.to_string(),
            SuccValue::Bool(v) => v.to_string(),
        };
        Some(format!(
            " {{ Ok(v___) => {{ {} {} }} Err(v___) => v___, }}",
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

    fn return_value(
        &self,
        orig: Option<String>,
        wbr: Option<&(Vec<String>, Vec<String>)>,
        lit_map: Option<(&String, &String)>,
        counter: &mut Counter,
    ) -> String {
        let mut values = vec![];
        if let Some((_, i)) = &self.first_return {
            let orig = orig.unwrap();
            let param = &self.index_map[i];
            let name = lit_map
                .and_then(|(n, v)| {
                    if *n == param.name && counter.simplify {
                        counter.direct_returns += 1;
                        Some((*v).clone())
                    } else {
                        None
                    }
                })
                .unwrap_or(format!("{}___v", param.name));
            let v = if let Some((may, must)) = wbr {
                if must.contains(&param.name) && counter.simplify {
                    counter.success_returns += 1;
                    format!("Ok({})", name)
                } else if !may.contains(&param.name) && counter.simplify {
                    counter.failure_returns += 1;
                    format!("Err({})", orig)
                } else {
                    format!(
                        "if {0}___s {{ Ok({1}) }} else {{ Err({2}) }}",
                        param.name, name, orig
                    )
                }
            } else {
                format!(
                    "if {0}___s {{ Ok({1}) }} else {{ Err({2}) }}",
                    param.name, name, orig
                )
            };
            values.push(v);
        } else if let Some(v) = orig {
            values.push(v);
        }
        for i in &self.remaining_return {
            let param = &self.index_map[i];
            let name = lit_map
                .and_then(|(n, v)| {
                    if *n == param.name && counter.simplify {
                        counter.direct_returns += 1;
                        Some((*v).clone())
                    } else {
                        None
                    }
                })
                .unwrap_or(format!("{}___v", param.name));
            let v = if param.must {
                name
            } else if let Some((may, must)) = wbr {
                if must.contains(&param.name) && counter.simplify {
                    counter.success_returns += 1;
                    format!("Some({})", name)
                } else if !may.contains(&param.name) && counter.simplify {
                    counter.failure_returns += 1;
                    "None".to_string()
                } else {
                    format!(
                        "if {0}___s {{ Some({1}) }} else {{ None }}",
                        param.name, name
                    )
                }
            } else {
                format!(
                    "if {0}___s {{ Some({1}) }} else {{ None }}",
                    param.name, name
                )
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

#[derive(Debug, Clone)]
struct Return {
    span: Span,
    value: Option<Span>,
}

#[derive(Debug, Clone)]
struct Call {
    hir_id: HirId,
    span: Span,
    callee: DefId,
    args: Vec<Arg>,
}

#[derive(Debug, Clone)]
struct Arg {
    span: Span,
    code: String,
}

#[derive(Debug)]
struct Ref {
    hir_id: HirId,
    span: Span,
    name: String,
}

#[derive(Debug)]
struct Assign {
    name: String,
    value: String,
    span: Span,
}

struct BodyVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    returns: Vec<Return>,
    calls: Vec<Call>,
    refs: Vec<Ref>,
    passes: Vec<String>,
    assigns: Vec<Assign>,
}

impl<'tcx> BodyVisitor<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            returns: vec![],
            calls: vec![],
            refs: vec![],
            passes: vec![],
            assigns: vec![],
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

    fn visit_expr_path(&mut self, expr: &'tcx Expr<'tcx>, path: QPath<'tcx>) {
        let source_map = self.tcx.sess.source_map();
        if let Ok(code) = source_map.span_to_snippet(path.qself_span()) {
            match get_parent(expr.hir_id, self.tcx) {
                Some(e) => {
                    if let ExprKind::Unary(UnOp::Deref, _) = e.kind {
                    } else {
                        self.passes.push(code)
                    }
                }
                None => self.passes.push(code),
            }
        }
    }

    fn visit_expr_unary(&mut self, expr: &'tcx Expr<'tcx>, e: &'tcx Expr<'tcx>) {
        let source_map = self.tcx.sess.source_map();
        self.refs.push(Ref {
            hir_id: expr.hir_id,
            span: expr.span,
            name: source_map.span_to_snippet(e.span).unwrap(),
        })
    }

    fn visit_expr_assign(
        &mut self,
        expr: &'tcx Expr<'tcx>,
        lhs: &'tcx Expr<'tcx>,
        rhs: &'tcx Expr<'tcx>,
    ) {
        let source_map = self.tcx.sess.source_map();
        if let ExprKind::Unary(UnOp::Deref, e) = lhs.kind {
            self.assigns.push(Assign {
                name: source_map.span_to_snippet(e.span).unwrap(),
                value: source_map.span_to_snippet(rhs.span).unwrap(),
                span: expr.span.with_hi(expr.span.hi() + BytePos(1)),
            });
        }
    }
}

impl<'tcx> HVisitor<'tcx> for BodyVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        match expr.kind {
            ExprKind::Ret(e) => self.visit_expr_ret(expr, e),
            ExprKind::Call(callee, args) => self.visit_expr_call(expr, callee, args),
            ExprKind::Path(path) => self.visit_expr_path(expr, path),
            ExprKind::Unary(UnOp::Deref, e) => self.visit_expr_unary(expr, e),
            ExprKind::Assign(lhs, rhs, _) => self.visit_expr_assign(expr, lhs, rhs),
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
            return Some(n.get());
        }
    }
    None
}

fn get_parent(hir_id: HirId, tcx: TyCtxt<'_>) -> Option<&Expr<'_>> {
    let Node::Expr(e) = tcx.parent_hir_node(hir_id) else {
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

fn get_parent_call(hir_id: HirId, tcx: TyCtxt<'_>) -> Option<&Expr<'_>> {
    let parent = get_parent(hir_id, tcx)?;
    if let ExprKind::Call(_, _) = parent.kind {
        Some(parent)
    } else {
        get_parent_call(parent.hir_id, tcx)
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

fn generate_set_flag(
    span: &Span,
    i: &usize,
    rcfws: &BTreeMap<String, Vec<Span>>,
    assign_map: &BTreeMap<usize, String>,
    counter: &mut Counter,
) -> String {
    if let Some(arg) = assign_map.get(i) {
        let rcfw = &rcfws.get(arg);
        if let Some(rcfw) = rcfw {
            if rcfw.iter().any(|sp| span.contains(*sp)) && counter.simplify {
                counter.removed_flag_sets += 1;
                return "".to_string();
            }
        }
        return format!("{}___s = true;", arg);
    }
    "".to_string()
}
