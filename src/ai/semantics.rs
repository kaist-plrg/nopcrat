use std::collections::{BTreeMap, BTreeSet};

use etrace::some_or;
use lazy_static::lazy_static;
use rustc_abi::{FieldIdx, Size, VariantIdx};
use rustc_const_eval::interpret::{AllocRange, ConstValue, GlobalAlloc, Scalar};
use rustc_middle::{
    mir::{
        AggregateKind, BasicBlock, BinOp, CastKind, Constant, ConstantKind, Location, Mutability,
        Operand, Place, PlaceElem, ProjectionElem, Rvalue, Statement, StatementKind, Terminator,
        TerminatorKind, UnOp,
    },
    ty::{adjustment::PointerCoercion, AdtKind, Ty, TyKind, TypeAndMut},
};
use rustc_span::def_id::DefId;
use rustc_type_ir::{FloatTy, IntTy, UintTy};

use super::{analysis::Label, domains::*};

#[allow(clippy::only_used_in_recursion)]
impl<'tcx> super::analysis::Analyzer<'tcx> {
    pub fn transfer_statement(&self, stmt: &Statement<'tcx>, state: &AbsState) -> AbsState {
        tracing::info!("\n{:?}", stmt);
        if let StatementKind::Assign(box (place, rvalue)) = &stmt.kind {
            let (new_v, reads) = self.transfer_rvalue(rvalue, state);
            let (mut new_state, writes) = self.assign(place, new_v, state);
            new_state.add_reads(reads.into_iter());
            new_state.add_writes(writes.into_iter());
            new_state
        } else {
            unreachable!("{:?}", stmt)
        }
    }

    fn assign(
        &self,
        place: &Place<'tcx>,
        new_v: AbsValue,
        state: &AbsState,
    ) -> (AbsState, Vec<AbsPath>) {
        let mut new_state = state.clone();
        let writes = if place.is_indirect_first_projection() {
            let projection = self.abstract_projection(&place.projection[1..], state);
            let ptr = state.local.get(place.local.index());
            self.indirect_assign(&ptr.ptrv, &new_v, &projection, &mut new_state);
            self.get_write_paths_of_ptr(&ptr.ptrv, &projection)
        } else {
            let old_v = new_state.local.get_mut(place.local.index());
            let projection = self.abstract_projection(place.projection, state);
            self.update_value(new_v, old_v, false, &projection);
            vec![]
        };
        (new_state, writes)
    }

    fn indirect_assign(
        &self,
        ptr: &AbsPtr,
        new_v: &AbsValue,
        projection: &[AbsProjElem],
        state: &mut AbsState,
    ) {
        if let AbsPtr::Set(ptrs) = ptr {
            let weak = ptrs.len() > 1;
            for ptr in ptrs {
                let old_v = some_or!(state.get_mut(ptr.base), continue);
                let mut ptr_projection = ptr.projection.clone();
                ptr_projection.extend(projection.to_owned());
                self.update_value(new_v.clone(), old_v, weak, &ptr_projection);
            }
        } else {
            tracing::warn!("indirect_assign to top");
        }
    }

    fn get_write_paths_of_ptr(&self, ptr: &AbsPtr, projection: &[AbsProjElem]) -> Vec<AbsPath> {
        if let AbsPtr::Set(ptrs) = ptr {
            if ptrs.len() == 1 {
                let mut ptr = ptrs.first().unwrap().clone();
                ptr.projection.extend(projection.to_owned());
                if let Some((path, false)) = AbsPath::from_place(&ptr, &self.alloc_param_map) {
                    return self.expands_path(&path);
                }
            }
        }
        vec![]
    }

    pub fn transfer_terminator(
        &mut self,
        terminator: &Terminator<'tcx>,
        state: &AbsState,
        label: &Label,
    ) -> (Vec<AbsState>, Vec<Location>) {
        tracing::info!("\n{:?}", terminator);
        match &terminator.kind {
            TerminatorKind::Goto { target } => (vec![state.clone()], vec![block_entry(*target)]),
            TerminatorKind::SwitchInt { discr, targets } => {
                let (v, reads) = self.transfer_operand(discr, state);
                let mut new_state = state.clone();
                new_state.add_reads(reads.into_iter());
                let locations = if v.intv.is_bot() && v.uintv.is_bot() {
                    v.boolv
                        .gamma()
                        .into_iter()
                        .map(|b| block_entry(targets.target_for_value(b as _)))
                        .collect()
                } else {
                    targets
                        .all_targets()
                        .iter()
                        .map(|target| block_entry(*target))
                        .collect()
                };
                (vec![new_state], locations)
            }
            TerminatorKind::UnwindResume => (vec![], vec![]),
            TerminatorKind::UnwindTerminate(_) => (vec![], vec![]),
            TerminatorKind::Return => (vec![], vec![]),
            TerminatorKind::Unreachable => (vec![], vec![]),
            TerminatorKind::Drop { target, .. } => {
                (vec![state.clone()], vec![block_entry(*target)])
            }
            TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                ..
            } => {
                let (func, mut reads) = self.transfer_operand(func, state);
                let (args, readss): (Vec<_>, Vec<_>) = args
                    .iter()
                    .map(|arg| self.transfer_operand(arg, state))
                    .unzip();
                for reads2 in readss {
                    reads.extend(reads2);
                }
                let new_states = if let Some(fns) = func.fnv.gamma() {
                    let mut new_states_map: BTreeMap<_, Vec<_>> = BTreeMap::new();
                    for def_id in fns {
                        let states = self.transfer_call(
                            *def_id,
                            &args,
                            destination,
                            state.clone(),
                            reads.clone(),
                            label,
                        );
                        for state in states {
                            let rw = state.rw.clone();
                            new_states_map.entry(rw).or_default().push(state);
                        }
                    }
                    new_states_map
                        .into_values()
                        .map(|states| states.into_iter().reduce(|a, b| a.join(&b)).unwrap())
                        .collect()
                } else {
                    tracing::warn!("call to top");
                    let (mut new_state, writes) = self.assign(destination, AbsValue::top(), state);
                    new_state.add_reads(reads.into_iter());
                    new_state.add_writes(writes.into_iter());
                    vec![new_state]
                };
                let locations = if new_states.is_empty() {
                    vec![]
                } else {
                    target
                        .as_ref()
                        .map(|target| vec![block_entry(*target)])
                        .unwrap_or(vec![])
                };
                (new_states, locations)
            }
            TerminatorKind::Assert { cond, target, .. } => {
                let (_, reads) = self.transfer_operand(cond, state);
                let mut new_state = state.clone();
                new_state.add_reads(reads.into_iter());
                (vec![new_state], vec![block_entry(*target)])
            }
            TerminatorKind::Yield { .. } => unreachable!("{:?}", terminator.kind),
            TerminatorKind::GeneratorDrop => unreachable!("{:?}", terminator.kind),
            TerminatorKind::FalseEdge { .. } => unreachable!("{:?}", terminator.kind),
            TerminatorKind::FalseUnwind { .. } => unreachable!("{:?}", terminator.kind),
            TerminatorKind::InlineAsm { .. } => unreachable!("{:?}", terminator.kind),
        }
    }

    fn transfer_call(
        &mut self,
        callee: DefId,
        args: &[AbsValue],
        dst: &Place<'tcx>,
        mut state: AbsState,
        mut reads: Vec<AbsPath>,
        label: &Label,
    ) -> Vec<AbsState> {
        let mut writes = vec![];
        let name = self.def_id_to_string(callee);
        let v = if callee.is_local() {
            if let Some(summary) = self.summaries.get(&callee) {
                if summary.return_states.is_empty() {
                    return vec![];
                }

                let mut ptr_maps = BTreeMap::new();
                let mut allocs = BTreeSet::new();
                for (param, arg) in summary.init_state.local.iter().skip(1).zip(args.iter()) {
                    for (param_ptr, arg_ptr) in param.compare_pointers(arg) {
                        let alloc = param_ptr.heap_addr();
                        let _ = ptr_maps.try_insert(alloc, arg_ptr.clone());
                        allocs.insert(alloc);
                    }
                }
                while let Some(alloc) = allocs.pop_first() {
                    let arg_ptr = ptr_maps.get(&alloc).unwrap();
                    let (arg, _) = self.read_ptr(arg_ptr, &[], &state);
                    let param = summary.init_state.heap.get(alloc);
                    for (param_ptr, arg_ptr) in param.compare_pointers(&arg) {
                        let alloc = param_ptr.heap_addr();
                        if ptr_maps.try_insert(alloc, arg_ptr.clone()).is_ok() {
                            allocs.insert(alloc);
                        }
                    }
                }

                let mut states = vec![];
                for return_state in &summary.return_states {
                    let mut state = state.clone();
                    let mut ptr_maps = ptr_maps.clone();
                    let ret_v = return_state.local.get(0);
                    let mut allocs: BTreeSet<_> = ptr_maps
                        .keys()
                        .map(|p| return_state.heap.get(*p))
                        .chain(std::iter::once(ret_v))
                        .flat_map(|v| v.allocs())
                        .collect();
                    let label_alloc_map = self
                        .label_user_fn_alloc_map
                        .entry((label.clone(), return_state.rw.clone()))
                        .or_default();
                    while let Some(alloc) = allocs.pop_first() {
                        ptr_maps.entry(alloc).or_insert_with(|| {
                            let alloc_v = return_state.heap.get(alloc);
                            allocs.extend(alloc_v.allocs());
                            let i = if let Some(i) = label_alloc_map.get(&alloc) {
                                if *i < state.heap.len() {
                                    let old_v = state.heap.get_mut(*i);
                                    *old_v = old_v.join(alloc_v);
                                    *i
                                } else {
                                    state.heap.push(alloc_v.clone())
                                }
                            } else {
                                state.heap.push(alloc_v.clone())
                            };
                            label_alloc_map.insert(alloc, i);
                            AbsPtr::alpha(AbsPlace::alloc(i))
                        });
                    }
                    for (p, a) in &ptr_maps {
                        let v = return_state.heap.get(*p).subst(&ptr_maps);
                        self.indirect_assign(a, &v, &[], &mut state);
                    }
                    let ret_v = ret_v.subst(&ptr_maps);
                    let (mut state, writes) = self.assign(dst, ret_v, &state);
                    let callee_reads: Vec<_> = return_state
                        .rw
                        .reads
                        .iter()
                        .filter_map(|read| {
                            let ptrs = if let AbsPtr::Set(ptrs) = &args[read.base() - 1].ptrv {
                                ptrs
                            } else {
                                return None;
                            };
                            Some(ptrs.iter().filter_map(|ptr| {
                                let (mut path, _) =
                                    AbsPath::from_place(ptr, &self.alloc_param_map)?;
                                path.0.extend(read.0[1..].to_owned());
                                Some(path)
                            }))
                        })
                        .flatten()
                        .collect();
                    let callee_writes: Vec<_> = return_state
                        .rw
                        .writes
                        .iter()
                        .filter_map(|write| {
                            let ptr = if let AbsPtr::Set(ptrs) = &args[write.base() - 1].ptrv {
                                if ptrs.len() == 1 {
                                    ptrs.first().unwrap()
                                } else {
                                    return None;
                                }
                            } else {
                                return None;
                            };
                            let (mut path, array_access) =
                                AbsPath::from_place(ptr, &self.alloc_param_map)?;
                            if array_access {
                                return None;
                            }
                            path.0.extend(write.0[1..].to_owned());
                            Some(path)
                        })
                        .collect();
                    state.add_reads(reads.clone().into_iter());
                    state.add_reads(callee_reads.into_iter());
                    state.add_writes(callee_writes.into_iter());
                    state.add_writes(writes.into_iter());
                    states.push(state)
                }
                return states;
            }

            let sig = self.tcx.fn_sig(callee).skip_binder();
            let inputs = sig.inputs().skip_binder();
            let output = sig.output().skip_binder();

            assert!(name.contains("{extern#0}"));
            let fn_name = name.split("::").last().unwrap();
            let (read_args, write_args) = if inputs.iter().all(|ty| ty.is_primitive())
                || fn_name == "free"
                || fn_name == "realloc"
            {
                (vec![], vec![])
            } else {
                let (const_ptrs, mut_ptrs): (Vec<_>, Vec<_>) = inputs
                    .iter()
                    .enumerate()
                    .filter_map(|(i, ty)| {
                        if let TyKind::RawPtr(TypeAndMut { ty, mutbl }) = ty.kind() {
                            if let TyKind::Adt(adt, _) = ty.kind() {
                                if self.def_id_to_string(adt.did()).ends_with("::_IO_FILE") {
                                    return None;
                                }
                            }
                            return Some((i, mutbl));
                        }
                        None
                    })
                    .partition(|(_, mutbl)| matches!(mutbl, Mutability::Not));
                let const_ptrs: Vec<_> = const_ptrs.into_iter().map(|(i, _)| i).collect();
                let mut_ptrs: Vec<_> = mut_ptrs.into_iter().map(|(i, _)| i).collect();
                if mut_ptrs.is_empty() || WRITE_FUNCTIONS.contains(fn_name) {
                    (const_ptrs, mut_ptrs)
                } else {
                    todo!("{:?}", callee)
                }
            };
            for arg in read_args {
                let reads2 = self.get_read_paths_of_ptr(&args[arg].ptrv, &[]);
                reads.extend(reads2);
            }
            for arg in write_args {
                let writes2 = self.get_write_paths_of_ptr(&args[arg].ptrv, &[]);
                writes.extend(writes2);
            }

            if output.is_primitive() || output.is_unit() || output.is_never() {
                self.top_value_of_ty(&output, None, &mut BTreeSet::new())
            } else if ALLOC_FUNCTIONS.contains(fn_name) {
                let i = if let Some(i) = self.label_alloc_map.get(label) {
                    if *i < state.heap.len() {
                        *state.heap.get_mut(*i) = AbsValue::top();
                        *i
                    } else {
                        state.heap.push(AbsValue::top())
                    }
                } else {
                    state.heap.push(AbsValue::top())
                };
                self.label_alloc_map.insert(label.clone(), i);
                AbsValue::ptr(AbsPtr::alpha(AbsPlace::alloc(i)))
            } else if RETURN_FIRST_FUNCTIONS.contains(fn_name) {
                args[0].clone()
            } else {
                todo!("{:?}", callee)
            }
        } else {
            match name.as_str() {
                "::slice::{impl#0}::as_mut_ptr" | "::slice::{impl#0}::as_ptr" => {
                    let ptr = if let Some(ptrs) = args[0].ptrv.gamma() {
                        AbsPtr::alphas(
                            ptrs.iter()
                                .cloned()
                                .map(|mut ptr| {
                                    let zero = AbsUint::alpha(0);
                                    ptr.projection.push(AbsProjElem::Index(zero));
                                    ptr
                                })
                                .collect(),
                        )
                    } else {
                        AbsPtr::Top
                    };
                    AbsValue::ptr(ptr)
                }
                "::ptr::mut_ptr::{impl#0}::offset" | "::ptr::const_ptr::{impl#0}::offset" => {
                    let ptr = if let Some(ptrs) = args[0].ptrv.gamma() {
                        AbsPtr::alphas(
                            ptrs.iter()
                                .cloned()
                                .map(|mut ptr| {
                                    let last = ptr.projection.last_mut();
                                    if let Some(AbsProjElem::Index(i)) = last {
                                        *i = i.to_i64().add(&args[1].intv).to_u64();
                                    }
                                    ptr
                                })
                                .collect(),
                        )
                    } else {
                        AbsPtr::Top
                    };
                    AbsValue::ptr(ptr)
                }
                "::ptr::mut_ptr::{impl#0}::is_null" | "::ptr::const_ptr::{impl#0}::is_null" => {
                    let b = if let Some(ptrs) = args[0].ptrv.gamma() {
                        AbsBool::alphas(ptrs.iter().map(|ptr| ptr.is_null()).collect())
                    } else {
                        AbsBool::Top
                    };
                    AbsValue::bools(b)
                }
                "::ptr::mut_ptr::{impl#0}::offset_from"
                | "::ptr::const_ptr::{impl#0}::offset_from" => AbsValue::int_top(),
                "::ptr::write_volatile" => {
                    self.indirect_assign(&args[0].ptrv, &args[1], &[], &mut state);
                    let writes2 = self.get_write_paths_of_ptr(&args[0].ptrv, &[]);
                    writes.extend(writes2);
                    AbsValue::top()
                }
                "::option::{impl#0}::is_some" => {
                    let (v, reads2) = self.read_ptr(&args[0].ptrv, &[], &state);
                    reads.extend(reads2);
                    let b = match v.optionv {
                        AbsOption::Top => AbsBool::Top,
                        AbsOption::Some(_) => AbsBool::True,
                        AbsOption::None => AbsBool::False,
                        AbsOption::Bot => AbsBool::Bot,
                    };
                    AbsValue::bools(b)
                }
                "::option::{impl#0}::unwrap" => match &args[0].optionv {
                    AbsOption::Top => AbsValue::top(),
                    AbsOption::Some(box v) => v.clone(),
                    _ => AbsValue::bot(),
                },
                "::mem::size_of" => AbsValue::uint_top(),
                "::panicking::begin_panic" => AbsValue::bot(),
                _ if name.ends_with("::wrapping_add") => args[0].add(&args[1]),
                _ if name.ends_with("::wrapping_sub") => args[0].sub(&args[1]),
                _ if name.ends_with("::wrapping_mul") => args[0].mul(&args[1]),
                _ if name.ends_with("::wrapping_div") => args[0].div(&args[1]),
                _ => todo!("{}", name),
            }
        };
        let (mut new_state, writes_ret) = self.assign(dst, v, &state);
        new_state.add_reads(reads.into_iter());
        new_state.add_writes(writes.into_iter());
        new_state.add_writes(writes_ret.into_iter());
        vec![new_state]
    }

    fn transfer_rvalue(&self, rvalue: &Rvalue<'tcx>, state: &AbsState) -> (AbsValue, Vec<AbsPath>) {
        match rvalue {
            Rvalue::Use(operand) => self.transfer_operand(operand, state),
            Rvalue::Repeat(operand, len) => {
                let (v, reads) = self.transfer_operand(operand, state);
                let len = len.try_to_scalar_int().unwrap().try_to_u64().unwrap();
                (AbsValue::list(vec![v; len as usize]), reads)
            }
            Rvalue::Ref(_, _, place) => {
                let v = if place.is_indirect_first_projection() {
                    let projection = self.abstract_projection(&place.projection[1..], state);
                    let ptr = state.local.get(place.local.index());
                    if let AbsPtr::Set(ptrs) = &ptr.ptrv {
                        AbsValue::ptr(AbsPtr::Set(
                            ptrs.iter()
                                .map(|ptr| {
                                    let mut ptr_projection = ptr.projection.clone();
                                    ptr_projection.extend(projection.clone());
                                    AbsPlace {
                                        base: ptr.base,
                                        projection: ptr_projection,
                                    }
                                })
                                .collect(),
                        ))
                    } else {
                        AbsValue::ptr(AbsPtr::Top)
                    }
                } else {
                    let place = self.abstract_place(place, state);
                    AbsValue::ptr(AbsPtr::alpha(place))
                };
                (v, vec![])
            }
            Rvalue::ThreadLocalRef(_) => unreachable!("{:?}", rvalue),
            Rvalue::AddressOf(_, place) => {
                assert_eq!(place.projection.len(), 1);
                assert!(place.is_indirect_first_projection());
                let v = state.local.get(place.local.index());
                (AbsValue::ptr(v.ptrv.clone()), vec![])
            }
            Rvalue::Len(_) => unreachable!("{:?}", rvalue),
            Rvalue::Cast(kind, operand, ty) => {
                let (v, reads) = self.transfer_operand(operand, state);
                let v = match kind {
                    CastKind::PointerExposeAddress => todo!("{:?}", rvalue),
                    CastKind::PointerFromExposedAddress => {
                        let zero: BTreeSet<u128> = [0].into_iter().collect();
                        assert_eq!(v.uintv.gamma().unwrap(), &zero);
                        AbsValue::ptr(AbsPtr::null())
                    }
                    CastKind::PointerCoercion(coercion) => match coercion {
                        PointerCoercion::ReifyFnPointer => v,
                        PointerCoercion::UnsafeFnPointer => unreachable!("{:?}", rvalue),
                        PointerCoercion::ClosureFnPointer(_) => unreachable!("{:?}", rvalue),
                        PointerCoercion::MutToConstPointer => v,
                        PointerCoercion::ArrayToPointer => {
                            if let AbsPtr::Set(ptrs) = v.ptrv {
                                AbsValue::ptr(AbsPtr::Set(
                                    ptrs.iter()
                                        .cloned()
                                        .map(|mut ptr| {
                                            let zero = AbsUint::alpha(0);
                                            ptr.projection.push(AbsProjElem::Index(zero));
                                            ptr
                                        })
                                        .collect(),
                                ))
                            } else {
                                AbsValue::ptr(AbsPtr::Top)
                            }
                        }
                        PointerCoercion::Unsize => v,
                    },
                    CastKind::DynStar => unreachable!("{:?}", rvalue),
                    CastKind::IntToInt | CastKind::FloatToInt => match ty.kind() {
                        TyKind::Int(int_ty) => match int_ty {
                            IntTy::Isize => v.to_i64(),
                            IntTy::I8 => v.to_i8(),
                            IntTy::I16 => v.to_i16(),
                            IntTy::I32 => v.to_i32(),
                            IntTy::I64 => v.to_i64(),
                            IntTy::I128 => v.to_i128(),
                        },
                        TyKind::Uint(uint_ty) => match uint_ty {
                            UintTy::Usize => v.to_u64(),
                            UintTy::U8 => v.to_u8(),
                            UintTy::U16 => v.to_u16(),
                            UintTy::U32 => v.to_u32(),
                            UintTy::U64 => v.to_u64(),
                            UintTy::U128 => v.to_u128(),
                        },
                        _ => unreachable!("{:?}", rvalue),
                    },
                    CastKind::FloatToFloat | CastKind::IntToFloat => {
                        if let TyKind::Float(float_ty) = ty.kind() {
                            match float_ty {
                                FloatTy::F32 => v.to_f32(),
                                FloatTy::F64 => v.to_f64(),
                            }
                        } else {
                            unreachable!("{:?}", rvalue)
                        }
                    }
                    CastKind::PtrToPtr => v,
                    CastKind::FnPtrToPtr => v,
                    CastKind::Transmute => v,
                };
                (v, reads)
            }
            Rvalue::BinaryOp(binop, box (l, r)) => {
                let (l, mut reads_l) = self.transfer_operand(l, state);
                let (r, reads_r) = self.transfer_operand(r, state);
                let v = match binop {
                    BinOp::Add => l.add(&r),
                    BinOp::AddUnchecked => unreachable!("{:?}", rvalue),
                    BinOp::Sub => l.sub(&r),
                    BinOp::SubUnchecked => unreachable!("{:?}", rvalue),
                    BinOp::Mul => l.mul(&r),
                    BinOp::MulUnchecked => unreachable!("{:?}", rvalue),
                    BinOp::Div => l.div(&r),
                    BinOp::Rem => l.rem(&r),
                    BinOp::BitXor => l.bit_xor(&r),
                    BinOp::BitAnd => l.bit_and(&r),
                    BinOp::BitOr => l.bit_or(&r),
                    BinOp::Shl => l.shl(&r),
                    BinOp::ShlUnchecked => unreachable!("{:?}", rvalue),
                    BinOp::Shr => l.shr(&r),
                    BinOp::ShrUnchecked => unreachable!("{:?}", rvalue),
                    BinOp::Eq => l.eq(&r),
                    BinOp::Lt => l.lt(&r),
                    BinOp::Le => l.le(&r),
                    BinOp::Ne => l.ne(&r),
                    BinOp::Ge => l.ge(&r),
                    BinOp::Gt => l.gt(&r),
                    BinOp::Offset => todo!("{:?}", rvalue),
                };
                reads_l.extend(reads_r);
                (v, reads_l)
            }
            Rvalue::CheckedBinaryOp(_, _) => unreachable!("{:?}", rvalue),
            Rvalue::NullaryOp(_, _) => unreachable!("{:?}", rvalue),
            Rvalue::UnaryOp(unary, operand) => {
                let (v, reads) = self.transfer_operand(operand, state);
                let v = match unary {
                    UnOp::Not => v.not(),
                    UnOp::Neg => v.neg(),
                };
                (v, reads)
            }
            Rvalue::Discriminant(_) => todo!("{:?}", rvalue),
            Rvalue::Aggregate(box kind, fields) => match kind {
                AggregateKind::Array(_) => {
                    let (vs, readss): (Vec<_>, Vec<_>) = fields
                        .iter()
                        .map(|operand| self.transfer_operand(operand, state))
                        .unzip();
                    let v = AbsValue::list(vs.into_iter().collect());
                    let reads = readss.into_iter().flatten().collect();
                    (v, reads)
                }
                AggregateKind::Tuple => unreachable!("{:?}", rvalue),
                AggregateKind::Adt(def_id, _, _, _, _) => {
                    let adt_def = self.tcx.adt_def(def_id);
                    match adt_def.adt_kind() {
                        AdtKind::Struct => {
                            let (vs, readss): (Vec<_>, Vec<_>) = fields
                                .iter()
                                .map(|operand| self.transfer_operand(operand, state))
                                .unzip();
                            let v = AbsValue::list(vs.into_iter().collect());
                            let reads = readss.into_iter().flatten().collect();
                            (v, reads)
                        }
                        AdtKind::Union => {
                            assert_eq!(fields.len(), 1);
                            let operand = &fields[FieldIdx::from_usize(0)];
                            let (v, reads) = self.transfer_operand(operand, state);
                            let variant = adt_def.variant(VariantIdx::from_usize(0));
                            let v =
                                AbsValue::list(variant.fields.iter().map(|_| v.clone()).collect());
                            (v, reads)
                        }
                        AdtKind::Enum => {
                            assert_eq!(
                                format!("{:?}", adt_def),
                                "std::option::Option",
                                "{:?}",
                                rvalue
                            );
                            if let Some(field) = fields.get(FieldIdx::from_usize(0)) {
                                let (v, reads) = self.transfer_operand(field, state);
                                let opt_v = if v.is_bot() {
                                    AbsOption::bot()
                                } else {
                                    AbsOption::some(v)
                                };
                                (AbsValue::option(opt_v), reads)
                            } else {
                                (AbsValue::option(AbsOption::None), vec![])
                            }
                        }
                    }
                }
                AggregateKind::Closure(_, _) => unreachable!("{:?}", rvalue),
                AggregateKind::Generator(_, _, _) => unreachable!("{:?}", rvalue),
            },
            Rvalue::ShallowInitBox(_, _) => unreachable!("{:?}", rvalue),
            Rvalue::CopyForDeref(place) => self.transfer_place(place, state),
        }
    }

    fn transfer_operand(
        &self,
        operand: &Operand<'tcx>,
        state: &AbsState,
    ) -> (AbsValue, Vec<AbsPath>) {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => self.transfer_place(place, state),
            Operand::Constant(constant) => (self.transfer_constant(constant), vec![]),
        }
    }

    fn transfer_place(&self, place: &Place<'tcx>, state: &AbsState) -> (AbsValue, Vec<AbsPath>) {
        if place.is_indirect_first_projection() {
            let projection = self.abstract_projection(&place.projection[1..], state);
            let ptr = state.local.get(place.local.index());
            self.read_ptr(&ptr.ptrv, &projection, state)
        } else {
            let v = state.local.get(place.local.index());
            let projection = self.abstract_projection(place.projection, state);
            (self.get_value(v, &projection), vec![])
        }
    }

    fn read_ptr(
        &self,
        ptr: &AbsPtr,
        projection: &[AbsProjElem],
        state: &AbsState,
    ) -> (AbsValue, Vec<AbsPath>) {
        let v = if let AbsPtr::Set(ptrs) = ptr {
            ptrs.iter()
                .filter_map(|ptr| {
                    let v = state.get(ptr.base)?;
                    let mut ptr_projection = ptr.projection.clone();
                    ptr_projection.extend(projection.to_owned());
                    Some(self.get_value(v, &ptr_projection))
                })
                .reduce(|v1, v2| v1.join(&v2))
                .unwrap_or(AbsValue::bot())
        } else {
            AbsValue::top()
        };
        (v, self.get_read_paths_of_ptr(ptr, projection))
    }

    fn get_read_paths_of_ptr(&self, ptr: &AbsPtr, projection: &[AbsProjElem]) -> Vec<AbsPath> {
        if let AbsPtr::Set(ptrs) = ptr {
            ptrs.iter()
                .cloned()
                .filter_map(|mut ptr| {
                    ptr.projection.extend(projection.to_owned());
                    AbsPath::from_place(&ptr, &self.alloc_param_map).map(|(path, _)| path)
                })
                .flat_map(|path| self.expands_path(&path))
                .collect()
        } else {
            vec![]
        }
    }

    fn transfer_constant(&self, constant: &Constant<'tcx>) -> AbsValue {
        match constant.literal {
            ConstantKind::Ty(_) => unreachable!("{:?}", constant),
            ConstantKind::Unevaluated(constant, ty) => {
                if let Ok(v) = self.tcx.const_eval_poly(constant.def) {
                    self.transfer_const_value(&v, &ty)
                } else {
                    self.top_value_of_ty(&ty, None, &mut BTreeSet::new())
                }
            }
            ConstantKind::Val(v, ty) => self.transfer_const_value(&v, &ty),
        }
    }

    pub fn transfer_const_value(&self, v: &ConstValue<'tcx>, ty: &Ty<'tcx>) -> AbsValue {
        match v {
            ConstValue::Scalar(s) => match s {
                Scalar::Int(i) => match ty.kind() {
                    TyKind::Int(int_ty) => {
                        let v = match int_ty {
                            IntTy::Isize => i.try_to_i64().unwrap() as _,
                            IntTy::I8 => i.try_to_i8().unwrap() as _,
                            IntTy::I16 => i.try_to_i16().unwrap() as _,
                            IntTy::I32 => i.try_to_i32().unwrap() as _,
                            IntTy::I64 => i.try_to_i64().unwrap() as _,
                            IntTy::I128 => i.try_to_i128().unwrap(),
                        };
                        AbsValue::int(v)
                    }
                    TyKind::Uint(uint_ty) => {
                        let v = match uint_ty {
                            UintTy::Usize => i.try_to_u64().unwrap() as _,
                            UintTy::U8 => i.try_to_u8().unwrap() as _,
                            UintTy::U16 => i.try_to_u16().unwrap() as _,
                            UintTy::U32 => i.try_to_u32().unwrap() as _,
                            UintTy::U64 => i.try_to_u64().unwrap() as _,
                            UintTy::U128 => i.try_to_u128().unwrap(),
                        };
                        AbsValue::uint(v)
                    }
                    TyKind::Float(float_ty) => {
                        let v = match float_ty {
                            FloatTy::F32 => f32::from_bits(i.try_to_u32().unwrap()) as _,
                            FloatTy::F64 => f64::from_bits(i.try_to_u64().unwrap()),
                        };
                        AbsValue::float(v)
                    }
                    TyKind::Bool => AbsValue::boolean(i.try_to_bool().unwrap()),
                    TyKind::Char => AbsValue::uint(i.try_to_u32().unwrap() as _),
                    _ => unreachable!("{:?}", ty),
                },
                Scalar::Ptr(ptr, _) => {
                    let alloc = self.tcx.global_alloc(ptr.provenance);
                    match alloc {
                        GlobalAlloc::Function(_) => unreachable!("{:?}", alloc),
                        GlobalAlloc::VTable(_, _) => unreachable!("{:?}", alloc),
                        GlobalAlloc::Static(def_id) => {
                            let i = self.static_allocs.get(&def_id).unwrap();
                            AbsValue::ptr(AbsPtr::alpha(AbsPlace::alloc(*i)))
                        }
                        GlobalAlloc::Memory(_) => {
                            let i = self.literal_allocs.get(&ptr.provenance).unwrap();
                            AbsValue::ptr(AbsPtr::alpha(AbsPlace::alloc(*i)))
                        }
                    }
                }
            },
            ConstValue::ZeroSized => {
                if let TyKind::FnDef(def_id, _) = ty.kind() {
                    AbsValue::func(AbsFn::alpha(*def_id))
                } else {
                    unreachable!("{:?}", v)
                }
            }
            ConstValue::Slice { data, start, end } => {
                let start = Size::from_bytes(*start);
                let size = Size::from_bytes(*end) - start;
                let range = AllocRange { start, size };
                let arr = data
                    .inner()
                    .get_bytes_strip_provenance(&self.tcx, range)
                    .unwrap();
                let msg = String::from_utf8(arr.to_vec()).unwrap();
                if msg == "explicit panic" {
                    AbsValue::top()
                } else {
                    unreachable!("{:?}", msg)
                }
            }
            ConstValue::ByRef { .. } => unreachable!("{:?}", v),
        }
    }

    pub fn top_value_of_ty(
        &self,
        ty: &Ty<'tcx>,
        mut heap: Option<&mut AbsHeap>,
        adts: &mut BTreeSet<DefId>,
    ) -> AbsValue {
        match ty.kind() {
            TyKind::Bool => AbsValue::bool_top(),
            TyKind::Char => unreachable!("{:?}", ty),
            TyKind::Int(_) => AbsValue::int_top(),
            TyKind::Uint(_) => AbsValue::uint_top(),
            TyKind::Float(_) => AbsValue::float_top(),
            TyKind::Adt(adt, arg) => match adt.adt_kind() {
                AdtKind::Struct | AdtKind::Union => {
                    let variant = adt.variant(VariantIdx::from_usize(0));
                    AbsValue::list(
                        variant
                            .fields
                            .iter()
                            .map(|field| {
                                let ty = field.ty(self.tcx, arg);
                                self.top_value_of_ty(&ty, heap.as_deref_mut(), adts)
                            })
                            .collect(),
                    )
                }
                AdtKind::Enum => {
                    let ty = format!("{:?}", adt);
                    match ty.as_str() {
                        "std::option::Option" => AbsValue::option(AbsOption::Top),
                        "libc::c_void" => AbsValue::top(),
                        _ => unreachable!("{:?}", ty),
                    }
                }
            },
            TyKind::Foreign(_) => AbsValue::top(),
            TyKind::Str => unreachable!("{:?}", ty),
            TyKind::Array(ty, len) => {
                let len = len.try_to_scalar_int().unwrap().try_to_u64().unwrap();
                AbsValue::list(
                    (0..len)
                        .map(|_| self.top_value_of_ty(ty, heap.as_deref_mut(), adts))
                        .collect(),
                )
            }
            TyKind::Slice(_) => unreachable!("{:?}", ty),
            TyKind::RawPtr(TypeAndMut { ty, .. }) | TyKind::Ref(_, ty, _) => {
                let def_id = if let Some(adt) = ty.ty_adt_def() {
                    let def_id = adt.did();
                    if adts.insert(def_id) {
                        Some(def_id)
                    } else {
                        return AbsValue::ptr(AbsPtr::Top);
                    }
                } else {
                    None
                };
                let v = self.top_value_of_ty(ty, heap.as_deref_mut(), adts);
                if let Some(def_id) = def_id {
                    adts.remove(&def_id);
                }
                let heap = heap.unwrap();
                let i = heap.push(v);
                AbsValue::ptr(AbsPtr::alpha(AbsPlace::alloc(i)))
            }
            TyKind::FnDef(_, _) => unreachable!("{:?}", ty),
            TyKind::FnPtr(_) => todo!("{:?}", ty),
            TyKind::Dynamic(_, _, _) => unreachable!("{:?}", ty),
            TyKind::Closure(_, _) => unreachable!("{:?}", ty),
            TyKind::Generator(_, _, _) => unreachable!("{:?}", ty),
            TyKind::GeneratorWitness(_) => unreachable!("{:?}", ty),
            TyKind::GeneratorWitnessMIR(_, _) => unreachable!("{:?}", ty),
            TyKind::Never => AbsValue::bot(),
            TyKind::Tuple(tys) => AbsValue::list(
                tys.iter()
                    .map(|ty| self.top_value_of_ty(&ty, heap.as_deref_mut(), adts))
                    .collect(),
            ),
            TyKind::Alias(_, _) => unreachable!("{:?}", ty),
            TyKind::Param(_) => unreachable!("{:?}", ty),
            TyKind::Bound(_, _) => unreachable!("{:?}", ty),
            TyKind::Placeholder(_) => unreachable!("{:?}", ty),
            TyKind::Infer(_) => unreachable!("{:?}", ty),
            TyKind::Error(_) => unreachable!("{:?}", ty),
        }
    }

    fn abstract_place(&self, place: &Place<'tcx>, state: &AbsState) -> AbsPlace {
        let base = AbsBase::Local(place.local.index());
        let projection = self.abstract_projection(place.projection, state);
        AbsPlace { base, projection }
    }

    fn abstract_projection(
        &self,
        projection: &[PlaceElem<'tcx>],
        state: &AbsState,
    ) -> Vec<AbsProjElem> {
        projection
            .iter()
            .map(|e| self.abstract_elem(e, state))
            .collect()
    }

    fn abstract_elem(&self, elem: &PlaceElem<'tcx>, state: &AbsState) -> AbsProjElem {
        match elem {
            ProjectionElem::Deref => todo!("{:?}", elem),
            ProjectionElem::Field(field, _) => AbsProjElem::Field(field.index()),
            ProjectionElem::Index(idx) => {
                AbsProjElem::Index(state.local.get(idx.index()).uintv.clone())
            }
            ProjectionElem::ConstantIndex { .. } => unreachable!("{:?}", elem),
            ProjectionElem::Subslice { .. } => unreachable!("{:?}", elem),
            ProjectionElem::Downcast(_, _) => unreachable!("{:?}", elem),
            ProjectionElem::OpaqueCast(_) => unreachable!("{:?}", elem),
        }
    }

    fn update_value(
        &self,
        new_v: AbsValue,
        old_v: &mut AbsValue,
        weak: bool,
        projection: &[AbsProjElem],
    ) {
        if let Some(first) = projection.first() {
            match first {
                AbsProjElem::Field(field) => {
                    if let Some(old_v) = old_v.listv.get_mut(*field) {
                        self.update_value(new_v, old_v, weak, &projection[1..]);
                    }
                }
                AbsProjElem::Index(idx) => {
                    if let AbsList::List(l) = &mut old_v.listv {
                        let (indices, new_weak): (Box<dyn Iterator<Item = usize>>, _) =
                            if let Some(indices) = idx.gamma() {
                                (Box::new(indices.iter().map(|i| *i as _)), indices.len() > 1)
                            } else {
                                (Box::new(0..l.len()), l.len() > 1)
                            };
                        let weak = weak || new_weak;
                        for idx in indices {
                            if let Some(old_v) = l.get_mut(idx) {
                                self.update_value(new_v.clone(), old_v, weak, &projection[1..]);
                            }
                        }
                    }
                }
            }
        } else if weak {
            *old_v = new_v.join(old_v);
        } else {
            *old_v = new_v;
        }
    }

    fn get_value(&self, v: &AbsValue, projection: &[AbsProjElem]) -> AbsValue {
        let first = some_or!(projection.first(), return v.clone());
        match first {
            AbsProjElem::Field(field) => match &v.listv {
                AbsList::Top => AbsValue::top(),
                AbsList::List(l) => self.get_value(&l[*field], &projection[1..]),
                AbsList::Bot => AbsValue::bot(),
            },
            AbsProjElem::Index(idx) => match &v.listv {
                AbsList::Top => {
                    if idx.is_bot() {
                        AbsValue::bot()
                    } else {
                        AbsValue::top()
                    }
                }
                AbsList::List(l) => {
                    let indices: Box<dyn Iterator<Item = usize>> =
                        if let Some(indices) = idx.gamma() {
                            Box::new(indices.iter().map(|i| *i as _))
                        } else {
                            Box::new(0..l.len())
                        };
                    indices
                        .filter_map(|index| {
                            l.get(index).map(|v| self.get_value(v, &projection[1..]))
                        })
                        .reduce(|v1, v2| v1.join(&v2))
                        .unwrap_or(AbsValue::bot())
                }
                AbsList::Bot => AbsValue::bot(),
            },
        }
    }
}

fn block_entry(block: BasicBlock) -> Location {
    Location {
        block,
        statement_index: 0,
    }
}

lazy_static! {
    static ref WRITE_FUNCTIONS: BTreeSet<&'static str> = [
        "__fxstat",
        "__xstat",
        "_setjmp",
        "getcwd",
        "getgroups",
        "getopt_long",
        "fgets",
        "fread",
        "longjmp",
        "memcpy",
        "regexec",
        "setvbuf",
        "sigaction",
        "sigaddset",
        "sigemptyset",
        "sigprocmask",
        "strcat",
        "strcpy",
        "strncpy",
        "strtol",
    ]
    .into_iter()
    .collect();
    static ref ALLOC_FUNCTIONS: BTreeSet<&'static str> = [
        "__ctype_b_loc",
        "__errno_location",
        "fopen",
        "malloc",
        "realloc",
        "getenv",
        "getpwnam",
        "getpwuid",
        "popen",
        "setlocale",
        "strerror",
        "tmpfile",
    ]
    .into_iter()
    .collect();
    static ref RETURN_FIRST_FUNCTIONS: BTreeSet<&'static str> = [
        "fgets", "getcwd", "memchr", "memcpy", "strcat", "strchr", "strcpy", "strncpy", "strrchr",
    ]
    .into_iter()
    .collect();
}
