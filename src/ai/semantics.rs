use std::collections::{BTreeMap, BTreeSet};

use etrace::some_or;
use rustc_abi::VariantIdx;
use rustc_const_eval::interpret::{ConstValue, Scalar};
use rustc_middle::{
    mir::{
        AggregateKind, BinOp, BorrowKind, CastKind, Constant, ConstantKind, MutBorrowKind, Operand,
        Place, PlaceElem, ProjectionElem, Rvalue, Statement, StatementKind, Terminator,
        TerminatorKind, UnOp,
    },
    ty::{Ty, TyKind, TypeAndMut},
};
use rustc_span::def_id::DefId;
use rustc_type_ir::{FloatTy, IntTy, UintTy};

use super::domains::*;

#[allow(clippy::only_used_in_recursion)]
impl<'tcx> super::analysis::Analyzer<'tcx> {
    pub fn transfer_statement(
        &self,
        stmt: &Statement<'tcx>,
        state: &AbsState,
        alloc_param_map: &BTreeMap<usize, usize>,
    ) -> AbsState {
        if let StatementKind::Assign(box (place, rvalue)) = &stmt.kind {
            let new_v = self.transfer_rvalue(rvalue, state);
            let mut new_state = state.clone();
            if place.is_indirect_first_projection() {
                let projection = self.abstract_projection(&place.projection[1..], state);
                let ptr = state.local.get(place.local.index());
                if let AbsPtr::Set(ptrs) = &ptr.ptrv {
                    let weak = ptrs.len() > 1;
                    for ptr in ptrs {
                        let old_v = new_state.get_mut(ptr.base).unwrap();
                        let mut ptr_projection = ptr.projection.clone();
                        ptr_projection.append(&mut projection.clone());
                        self.update_value(new_v.clone(), old_v, weak, &projection);
                    }
                    if ptrs.len() == 1 {
                        let mut ptr = ptrs.first().unwrap().clone();
                        ptr.projection.append(&mut projection.clone());
                        if let Some((path, false)) = AbsPath::from_place(&ptr, alloc_param_map) {
                            let paths = self.expands_path(&path);
                            println!("{:?}", paths);
                        }
                    }
                } else {
                    todo!("{:?}", stmt);
                }
            } else {
                let old_v = new_state.local.get_mut(place.local.index());
                let projection = self.abstract_projection(place.projection, state);
                self.update_value(new_v, old_v, false, &projection);
            }
            new_state
        } else {
            unreachable!("{:?}", stmt)
        }
    }

    pub fn transfer_terminator(&self, terminator: &Terminator<'tcx>, state: &AbsState) -> AbsState {
        match &terminator.kind {
            TerminatorKind::Goto { .. } => state.clone(),
            TerminatorKind::SwitchInt { .. } => state.clone(),
            TerminatorKind::UnwindResume => state.clone(),
            TerminatorKind::UnwindTerminate(_) => state.clone(),
            TerminatorKind::Return => state.clone(),
            TerminatorKind::Unreachable => state.clone(),
            TerminatorKind::Drop { .. } => state.clone(),
            TerminatorKind::Call { .. } => todo!("{:?}", terminator.kind),
            TerminatorKind::Assert { .. } => state.clone(),
            TerminatorKind::Yield { .. } => unreachable!("{:?}", terminator.kind),
            TerminatorKind::GeneratorDrop => unreachable!("{:?}", terminator.kind),
            TerminatorKind::FalseEdge { .. } => unreachable!("{:?}", terminator.kind),
            TerminatorKind::FalseUnwind { .. } => unreachable!("{:?}", terminator.kind),
            TerminatorKind::InlineAsm { .. } => unreachable!("{:?}", terminator.kind),
        }
    }

    fn transfer_rvalue(&self, rvalue: &Rvalue<'tcx>, state: &AbsState) -> AbsValue {
        match rvalue {
            Rvalue::Use(operand) => self.transfer_operand(operand, state),
            Rvalue::Repeat(operand, len) => {
                let v = self.transfer_operand(operand, state);
                let len = len.try_to_scalar_int().unwrap().try_to_u128().unwrap();
                AbsValue::list(vec![v; len as usize])
            }
            Rvalue::Ref(_, kind, place) => {
                assert!(matches!(
                    kind,
                    BorrowKind::Mut {
                        kind: MutBorrowKind::Default
                    }
                ));
                if place.is_indirect_first_projection() {
                    let projection = self.abstract_projection(&place.projection[1..], state);
                    let ptr = state.local.get(place.local.index());
                    if let AbsPtr::Set(ptrs) = &ptr.ptrv {
                        AbsValue::ptr(AbsPtr::Set(
                            ptrs.iter()
                                .map(|ptr| {
                                    let mut ptr_projection = ptr.projection.clone();
                                    ptr_projection.append(&mut projection.clone());
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
                }
            }
            Rvalue::ThreadLocalRef(_) => unreachable!("{:?}", rvalue),
            Rvalue::AddressOf(_, place) => {
                assert_eq!(place.projection.len(), 1);
                assert!(place.is_indirect_first_projection());
                let v = state.local.get(place.local.index());
                AbsValue::ptr(v.ptrv.clone())
            }
            Rvalue::Len(_) => unreachable!("{:?}", rvalue),
            Rvalue::Cast(kind, operand, ty) => {
                let v = self.transfer_operand(operand, state);
                match kind {
                    CastKind::PointerExposeAddress => todo!("{:?}", rvalue),
                    CastKind::PointerFromExposedAddress => todo!("{:?}", rvalue),
                    CastKind::PointerCoercion(_) => todo!("{:?}", rvalue),
                    CastKind::DynStar => todo!("{:?}", rvalue),
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
                    CastKind::PtrToPtr => todo!("{:?}", rvalue),
                    CastKind::FnPtrToPtr => todo!("{:?}", rvalue),
                    CastKind::Transmute => todo!("{:?}", rvalue),
                }
            }
            Rvalue::BinaryOp(binop, box (l, r)) => {
                let l = self.transfer_operand(l, state);
                let r = self.transfer_operand(r, state);
                match binop {
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
                }
            }
            Rvalue::CheckedBinaryOp(_, _) => unreachable!("{:?}", rvalue),
            Rvalue::NullaryOp(_, _) => unreachable!("{:?}", rvalue),
            Rvalue::UnaryOp(unary, operand) => {
                let v = self.transfer_operand(operand, state);
                match unary {
                    UnOp::Not => v.not(),
                    UnOp::Neg => v.neg(),
                }
            }
            Rvalue::Discriminant(_) => todo!("{:?}", rvalue),
            Rvalue::Aggregate(box kind, fields) => match kind {
                AggregateKind::Array(_) => AbsValue::list(
                    fields
                        .iter()
                        .map(|operand| self.transfer_operand(operand, state))
                        .collect(),
                ),
                AggregateKind::Tuple => unreachable!("{:?}", rvalue),
                AggregateKind::Adt(def_id, _, _, _, _) => {
                    assert!(def_id.is_local());
                    AbsValue::list(
                        fields
                            .iter()
                            .map(|operand| self.transfer_operand(operand, state))
                            .collect(),
                    )
                }
                AggregateKind::Closure(_, _) => unreachable!("{:?}", rvalue),
                AggregateKind::Generator(_, _, _) => unreachable!("{:?}", rvalue),
            },
            Rvalue::ShallowInitBox(_, _) => unreachable!("{:?}", rvalue),
            Rvalue::CopyForDeref(place) => self.transfer_place(place, state),
        }
    }

    fn transfer_operand(&self, operand: &Operand<'tcx>, state: &AbsState) -> AbsValue {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => self.transfer_place(place, state),
            Operand::Constant(constant) => self.transfer_constant(constant),
        }
    }

    fn transfer_place(&self, place: &Place<'tcx>, state: &AbsState) -> AbsValue {
        if place.is_indirect_first_projection() {
            let projection = self.abstract_projection(&place.projection[1..], state);
            let ptr = state.local.get(place.local.index());
            if let AbsPtr::Set(ptrs) = &ptr.ptrv {
                ptrs.iter()
                    .map(|ptr| {
                        let v = state.get(ptr.base).unwrap();
                        let mut ptr_projection = ptr.projection.clone();
                        ptr_projection.append(&mut projection.clone());
                        self.get_value(v, &projection)
                    })
                    .reduce(|v1, v2| v1.join(&v2))
                    .unwrap_or(AbsValue::bot())
            } else {
                AbsValue::top()
            }
        } else {
            let v = state.local.get(place.local.index());
            let projection = self.abstract_projection(place.projection, state);
            self.get_value(v, &projection)
        }
    }

    fn transfer_constant(&self, constant: &Constant<'tcx>) -> AbsValue {
        match constant.literal {
            ConstantKind::Ty(_) => unreachable!("{:?}", constant),
            ConstantKind::Unevaluated(_, ty) => {
                self.top_value_of_ty(&ty, None, &mut BTreeSet::new())
            }
            ConstantKind::Val(v, ty) => {
                if let ConstValue::Scalar(s) = v {
                    match s {
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
                            _ => unreachable!("{:?}", ty),
                        },
                        Scalar::Ptr(_, _) => todo!("{:?}", constant),
                    }
                } else {
                    unreachable!("{:?}", constant)
                }
            }
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
            TyKind::Adt(adt, arg) => {
                assert!(adt.did().is_local());
                assert!(adt.is_struct());
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
            TyKind::Foreign(_) => unreachable!("{:?}", ty),
            TyKind::Str => unreachable!("{:?}", ty),
            TyKind::Array(ty, len) => {
                let v = self.top_value_of_ty(ty, heap, adts);
                let len = len.try_to_scalar_int().unwrap().try_to_u128().unwrap();
                AbsValue::list(vec![v; len as usize])
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
                let ptr = AbsPlace {
                    base: AbsBase::Heap(i),
                    projection: vec![],
                };
                AbsValue::ptr(AbsPtr::alpha(ptr))
            }
            TyKind::FnDef(_, _) => unreachable!("{:?}", ty),
            TyKind::FnPtr(_) => todo!("{:?}", ty),
            TyKind::Dynamic(_, _, _) => unreachable!("{:?}", ty),
            TyKind::Closure(_, _) => unreachable!("{:?}", ty),
            TyKind::Generator(_, _, _) => unreachable!("{:?}", ty),
            TyKind::GeneratorWitness(_) => unreachable!("{:?}", ty),
            TyKind::GeneratorWitnessMIR(_, _) => unreachable!("{:?}", ty),
            TyKind::Never => unreachable!("{:?}", ty),
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
