use rustc_const_eval::interpret::{ConstValue, Scalar};
use rustc_middle::{
    mir::{
        BinOp, Constant, ConstantKind, Operand, Place, Rvalue, Statement, StatementKind,
        Terminator, TerminatorKind, UnOp,
    },
    ty::TyKind,
};
use rustc_type_ir::{FloatTy, IntTy, UintTy};

use super::domains::*;

pub fn transfer_statement(stmt: &Statement<'_>, state: &AbsState) -> AbsState {
    if let StatementKind::Assign(box (place, rvalue)) = &stmt.kind {
        let v = transfer_rvalue(rvalue, state);
        assert!(place.projection.is_empty());
        let mut state = state.clone();
        state.local.set(place.local.index(), v);
        state
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
        Rvalue::Cast(_, _, _) => todo!("{:?}", rvalue),
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
        Rvalue::Aggregate(_, _) => todo!("{:?}", rvalue),
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
    assert!(place.projection.is_empty());
    state.local.get(place.local.index()).clone()
}

pub fn transfer_constant(constant: &Constant<'_>, _state: &AbsState) -> AbsValue {
    match constant.literal {
        ConstantKind::Ty(_) => unreachable!("{:?}", constant),
        ConstantKind::Unevaluated(_, _) => todo!("{:?}", constant),
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
