use rustc_const_eval::interpret::{ConstValue, Scalar};
use rustc_middle::{
    mir::{BinOp, Constant, ConstantKind, Operand, Place, Rvalue, Statement, StatementKind},
    ty::TyKind,
};

use super::domains::*;

pub fn transfer_statement(stmt: &Statement<'_>, state: &AbsState) -> AbsState {
    if let StatementKind::Assign(box (place, rvalue)) = &stmt.kind {
        let v = transfer_rvalue(rvalue, state);
        assert!(place.projection.is_empty());
        let mut state = state.clone();
        state.local.0[place.local.index()] = v;
        state
    } else {
        unreachable!("{:?}", stmt)
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
                BinOp::Add | BinOp::AddUnchecked => l.add(&r),
                BinOp::Sub | BinOp::SubUnchecked => l.sub(&r),
                BinOp::Mul | BinOp::MulUnchecked => l.mul(&r),
                BinOp::Div => l.div(&r),
                BinOp::Rem => l.rem(&r),
                BinOp::BitXor => l.bit_xor(&r),
                BinOp::BitAnd => l.bit_and(&r),
                BinOp::BitOr => l.bit_or(&r),
                BinOp::Shl | BinOp::ShlUnchecked => l.shl(&r),
                BinOp::Shr | BinOp::ShrUnchecked => l.shr(&r),
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
        Rvalue::UnaryOp(_, _) => todo!("{:?}", rvalue),
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
    state.local.0[place.local.index()].clone()
}

pub fn transfer_constant(constant: &Constant<'_>, _state: &AbsState) -> AbsValue {
    match constant.literal {
        ConstantKind::Ty(_) => unreachable!("{:?}", constant),
        ConstantKind::Unevaluated(_, _) => todo!("{:?}", constant),
        ConstantKind::Val(v, ty) => {
            if let ConstValue::Scalar(s) = v {
                match s {
                    Scalar::Int(i) => match ty.kind() {
                        TyKind::Int(_) => AbsValue::int(i.try_to_i128().unwrap()),
                        TyKind::Uint(_) => AbsValue::uint(i.try_to_u128().unwrap()),
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
