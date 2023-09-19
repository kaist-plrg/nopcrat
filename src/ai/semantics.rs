use rustc_const_eval::interpret::{ConstValue, Scalar};
use rustc_middle::{
    mir::{
        AggregateKind, BinOp, CastKind, Constant, ConstantKind, Operand, Place, PlaceElem,
        ProjectionElem, Rvalue, Statement, StatementKind, Terminator, TerminatorKind, UnOp,
    },
    ty::{Ty, TyKind},
};
use rustc_type_ir::{FloatTy, IntTy, UintTy};

use super::domains::*;

pub fn transfer_statement(stmt: &Statement<'_>, state: &AbsState) -> AbsState {
    if let StatementKind::Assign(box (place, rvalue)) = &stmt.kind {
        let new_v = transfer_rvalue(rvalue, state);
        let mut new_state = state.clone();
        let old_v = new_state.local.get_mut(place.local.index());
        update_value(new_v, old_v, false, place.projection, state);
        new_state
    } else {
        unreachable!("{:?}", stmt)
    }
}

pub fn transfer_terminator(terminator: &Terminator<'_>, state: &AbsState) -> AbsState {
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

pub fn transfer_rvalue(rvalue: &Rvalue<'_>, state: &AbsState) -> AbsValue {
    match rvalue {
        Rvalue::Use(operand) => transfer_operand(operand, state),
        Rvalue::Repeat(operand, len) => {
            let v = transfer_operand(operand, state);
            let len = len.try_to_scalar_int().unwrap().try_to_u128().unwrap();
            AbsValue::list(vec![v; len as usize])
        }
        Rvalue::Ref(_, _, _) => todo!("{:?}", rvalue),
        Rvalue::ThreadLocalRef(_) => unreachable!("{:?}", rvalue),
        Rvalue::AddressOf(_, _) => todo!("{:?}", rvalue),
        Rvalue::Len(_) => unreachable!("{:?}", rvalue),
        Rvalue::Cast(kind, operand, ty) => {
            let v = transfer_operand(operand, state);
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
            let l = transfer_operand(l, state);
            let r = transfer_operand(r, state);
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
            let v = transfer_operand(operand, state);
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
                    .map(|operand| transfer_operand(operand, state))
                    .collect(),
            ),
            AggregateKind::Tuple => unreachable!("{:?}", rvalue),
            AggregateKind::Adt(def_id, _, _, _, _) => {
                assert!(def_id.is_local());
                AbsValue::list(
                    fields
                        .iter()
                        .map(|operand| transfer_operand(operand, state))
                        .collect(),
                )
            }
            AggregateKind::Closure(_, _) => unreachable!("{:?}", rvalue),
            AggregateKind::Generator(_, _, _) => unreachable!("{:?}", rvalue),
        },
        Rvalue::ShallowInitBox(_, _) => unreachable!("{:?}", rvalue),
        Rvalue::CopyForDeref(_) => todo!("{:?}", rvalue),
    }
}

pub fn transfer_operand(operand: &Operand<'_>, state: &AbsState) -> AbsValue {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => transfer_place(place, state),
        Operand::Constant(constant) => transfer_constant(constant, state),
    }
}

pub fn transfer_place(place: &Place<'_>, state: &AbsState) -> AbsValue {
    let v = state.local.get(place.local.index());
    get_value(v, place.projection, state)
}

pub fn transfer_constant(constant: &Constant<'_>, _state: &AbsState) -> AbsValue {
    match constant.literal {
        ConstantKind::Ty(_) => unreachable!("{:?}", constant),
        ConstantKind::Unevaluated(_, ty) => top_value_of_ty(&ty),
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

pub fn top_value_of_ty(ty: &Ty<'_>) -> AbsValue {
    match ty.kind() {
        TyKind::Bool => AbsValue::bool_top(),
        TyKind::Char => unreachable!("{:?}", ty),
        TyKind::Int(_) => AbsValue::int_top(),
        TyKind::Uint(_) => AbsValue::uint_top(),
        TyKind::Float(_) => AbsValue::float_top(),
        TyKind::Adt(_, _) => todo!("{:?}", ty),
        TyKind::Foreign(_) => unreachable!("{:?}", ty),
        TyKind::Str => unreachable!("{:?}", ty),
        TyKind::Array(ty, len) => {
            let v = top_value_of_ty(ty);
            let len = len.try_to_scalar_int().unwrap().try_to_u128().unwrap();
            AbsValue::list(vec![v; len as usize])
        }
        TyKind::Slice(_) => unreachable!("{:?}", ty),
        TyKind::RawPtr(_) => todo!("{:?}", ty),
        TyKind::Ref(_, _, _) => todo!("{:?}", ty),
        TyKind::FnDef(_, _) => unreachable!("{:?}", ty),
        TyKind::FnPtr(_) => todo!("{:?}", ty),
        TyKind::Dynamic(_, _, _) => unreachable!("{:?}", ty),
        TyKind::Closure(_, _) => unreachable!("{:?}", ty),
        TyKind::Generator(_, _, _) => unreachable!("{:?}", ty),
        TyKind::GeneratorWitness(_) => unreachable!("{:?}", ty),
        TyKind::GeneratorWitnessMIR(_, _) => unreachable!("{:?}", ty),
        TyKind::Never => unreachable!("{:?}", ty),
        TyKind::Tuple(tys) => AbsValue::list(tys.iter().map(|ty| top_value_of_ty(&ty)).collect()),
        TyKind::Alias(_, _) => unreachable!("{:?}", ty),
        TyKind::Param(_) => unreachable!("{:?}", ty),
        TyKind::Bound(_, _) => unreachable!("{:?}", ty),
        TyKind::Placeholder(_) => unreachable!("{:?}", ty),
        TyKind::Infer(_) => unreachable!("{:?}", ty),
        TyKind::Error(_) => unreachable!("{:?}", ty),
    }
}

fn update_value(
    new_v: AbsValue,
    old_v: &mut AbsValue,
    weak: bool,
    projection: &[PlaceElem<'_>],
    state: &AbsState,
) {
    if let Some(first) = projection.first() {
        match first {
            ProjectionElem::Deref => todo!("{:?}", projection),
            ProjectionElem::Field(field, _) => {
                if let Some(old_v) = old_v.listv.get_mut(field.index()) {
                    update_value(new_v, old_v, weak, &projection[1..], state);
                }
            }
            ProjectionElem::Index(idx) => {
                let idx = state.local.get(idx.index());
                if let Some(indices) = idx.uintv.gamma() {
                    if indices.len() == 1 {
                        let idx = indices.first().unwrap();
                        if let Some(old_v) = old_v.listv.get_mut(*idx as _) {
                            update_value(new_v, old_v, weak, &projection[1..], state);
                        }
                    } else {
                        for idx in indices {
                            if let Some(old_v) = old_v.listv.get_mut(*idx as _) {
                                update_value(new_v.clone(), old_v, true, &projection[1..], state);
                            }
                        }
                    }
                } else if let Some(len) = old_v.listv.len() {
                    for idx in 0..len {
                        if let Some(old_v) = old_v.listv.get_mut(idx) {
                            update_value(new_v.clone(), old_v, true, &projection[1..], state);
                        }
                    }
                }
            }
            ProjectionElem::ConstantIndex { .. } => unreachable!("{:?}", projection),
            ProjectionElem::Subslice { .. } => unreachable!("{:?}", projection),
            ProjectionElem::Downcast(_, _) => unreachable!("{:?}", projection),
            ProjectionElem::OpaqueCast(_) => unreachable!("{:?}", projection),
        }
    } else if weak {
        *old_v = new_v.join(old_v);
    } else {
        *old_v = new_v;
    }
}

fn get_value(v: &AbsValue, projection: &[PlaceElem<'_>], state: &AbsState) -> AbsValue {
    if let Some(first) = projection.first() {
        match first {
            ProjectionElem::Deref => todo!("{:?}", projection),
            ProjectionElem::Field(field, ty) => match &v.listv {
                AbsList::Top => top_value_of_ty(ty),
                AbsList::List(l) => {
                    let v = &l[field.index()];
                    get_value(v, &projection[1..], state)
                }
                AbsList::Bot => AbsValue::bot(),
            },
            ProjectionElem::Index(idx) => {
                let idx = state.local.get(idx.index());
                if let Some(indices) = idx.uintv.gamma() {
                    indices
                        .iter()
                        .map(|index| match &v.listv {
                            AbsList::Top => AbsValue::top(),
                            AbsList::List(l) => {
                                if let Some(v) = l.get(*index as usize) {
                                    get_value(v, &projection[1..], state)
                                } else {
                                    AbsValue::bot()
                                }
                            }
                            AbsList::Bot => AbsValue::bot(),
                        })
                        .reduce(|v1, v2| v1.join(&v2))
                        .unwrap_or(AbsValue::bot())
                } else {
                    match &v.listv {
                        AbsList::Top => AbsValue::top(),
                        AbsList::List(l) => l
                            .iter()
                            .map(|v| get_value(v, &projection[1..], state))
                            .reduce(|v1, v2| v1.join(&v2))
                            .unwrap_or(AbsValue::bot()),
                        AbsList::Bot => AbsValue::bot(),
                    }
                }
            }
            ProjectionElem::ConstantIndex { .. } => unreachable!("{:?}", projection),
            ProjectionElem::Subslice { .. } => unreachable!("{:?}", projection),
            ProjectionElem::Downcast(_, _) => unreachable!("{:?}", projection),
            ProjectionElem::OpaqueCast(_) => unreachable!("{:?}", projection),
        }
    } else {
        v.clone()
    }
}
