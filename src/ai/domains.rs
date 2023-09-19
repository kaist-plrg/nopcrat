use std::collections::{BTreeMap, BTreeSet};

use rustc_abi::FieldIdx;
use rustc_span::def_id::DefId;

#[derive(Debug, Clone)]
pub struct AbsState {
    pub local: AbsLocal,
    pub heap: AbsHeap,
}

impl AbsState {
    pub fn bot(len: usize) -> Self {
        Self {
            local: AbsLocal::bot(len),
            heap: AbsHeap::bot(),
        }
    }

    pub fn join(&self, other: &Self) -> Self {
        Self {
            local: self.local.join(&other.local),
            heap: self.heap.join(&other.heap),
        }
    }

    pub fn ord(&self, other: &Self) -> bool {
        self.local.ord(&other.local) && self.heap.ord(&other.heap)
    }
}

#[derive(Debug, Clone)]
pub struct AbsHeap(pub Vec<AbsValue>);

impl AbsHeap {
    pub fn bot() -> Self {
        Self(vec![])
    }

    pub fn join(&self, other: &Self) -> Self {
        Self(
            (0..self.0.len().max(other.0.len()))
                .map(|i| {
                    let bot = AbsValue::bot();
                    let v1 = self.0.get(i).unwrap_or(&bot);
                    let v2 = other.0.get(i).unwrap_or(&bot);
                    v1.join(v2)
                })
                .collect(),
        )
    }

    pub fn ord(&self, other: &Self) -> bool {
        self.0.len() <= other.0.len() && self.0.iter().zip(other.0.iter()).all(|(x, y)| x.ord(y))
    }
}

#[derive(Debug, Clone)]
pub struct AbsLocal(Vec<AbsValue>);

impl AbsLocal {
    pub fn bot(len: usize) -> Self {
        Self(vec![AbsValue::bot(); len])
    }

    pub fn join(&self, other: &Self) -> Self {
        assert_eq!(self.0.len(), other.0.len());
        Self(
            self.0
                .iter()
                .zip(other.0.iter())
                .map(|(x, y)| x.join(y))
                .collect(),
        )
    }

    pub fn ord(&self, other: &Self) -> bool {
        assert_eq!(self.0.len(), other.0.len());
        self.0.iter().zip(other.0.iter()).all(|(x, y)| x.ord(y))
    }

    pub fn get(&self, i: usize) -> &AbsValue {
        &self.0[i]
    }

    pub fn set(&mut self, i: usize, v: AbsValue) {
        self.0[i] = v;
    }
}

#[derive(Clone)]
pub struct AbsValue {
    pub intv: AbsInt,
    pub uintv: AbsUint,
    pub floatv: AbsFloat,
    pub boolv: AbsBool,
    pub listv: AbsList,
    pub ptrv: AbsPtr,
    pub adtv: AbsAdt,
    pub optionv: AbsOption,
    pub fnv: AbsFn,
}

impl std::fmt::Debug for AbsValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut not_bot = false;
        if !self.intv.is_bot() {
            write!(f, "{:?}", self.intv)?;
            not_bot = true;
        }
        if !self.uintv.is_bot() {
            if not_bot {
                write!(f, " | ")?;
            }
            write!(f, "{:?}", self.uintv)?;
            not_bot = true;
        }
        if !self.floatv.is_bot() {
            if not_bot {
                write!(f, " | ")?;
            }
            write!(f, "{:?}", self.floatv)?;
            not_bot = true;
        }
        if !self.boolv.is_bot() {
            if not_bot {
                write!(f, " | ")?;
            }
            write!(f, "{:?}", self.boolv)?;
            not_bot = true;
        }
        if !self.listv.is_bot() {
            if not_bot {
                write!(f, " | ")?;
            }
            write!(f, "{:?}", self.listv)?;
            not_bot = true;
        }
        if !self.ptrv.is_bot() {
            if not_bot {
                write!(f, " | ")?;
            }
            write!(f, "{:?}", self.ptrv)?;
            not_bot = true;
        }
        if !self.adtv.is_bot() {
            if not_bot {
                write!(f, " | ")?;
            }
            write!(f, "{:?}", self.adtv)?;
            not_bot = true;
        }
        if !self.optionv.is_bot() {
            if not_bot {
                write!(f, " | ")?;
            }
            write!(f, "{:?}", self.optionv)?;
            not_bot = true;
        }
        if !self.fnv.is_bot() {
            if not_bot {
                write!(f, " | ")?;
            }
            write!(f, "{:?}", self.fnv)?;
            not_bot = true;
        }
        if !not_bot {
            write!(f, "Bot")?;
        }
        Ok(())
    }
}

impl AbsValue {
    pub fn top() -> Self {
        Self {
            intv: AbsInt::top(),
            uintv: AbsUint::top(),
            floatv: AbsFloat::top(),
            boolv: AbsBool::top(),
            listv: AbsList::top(),
            ptrv: AbsPtr::top(),
            adtv: AbsAdt::top(),
            optionv: AbsOption::top(),
            fnv: AbsFn::top(),
        }
    }

    pub fn bot() -> Self {
        Self {
            intv: AbsInt::bot(),
            uintv: AbsUint::bot(),
            floatv: AbsFloat::bot(),
            boolv: AbsBool::bot(),
            listv: AbsList::bot(),
            ptrv: AbsPtr::bot(),
            adtv: AbsAdt::bot(),
            optionv: AbsOption::bot(),
            fnv: AbsFn::bot(),
        }
    }

    pub fn join(&self, other: &Self) -> Self {
        Self {
            intv: self.intv.join(&other.intv),
            uintv: self.uintv.join(&other.uintv),
            floatv: self.floatv.join(&other.floatv),
            boolv: self.boolv.join(&other.boolv),
            listv: self.listv.join(&other.listv),
            ptrv: self.ptrv.join(&other.ptrv),
            adtv: self.adtv.join(&other.adtv),
            optionv: self.optionv.join(&other.optionv),
            fnv: self.fnv.join(&other.fnv),
        }
    }

    pub fn ord(&self, other: &Self) -> bool {
        self.intv.ord(&other.intv)
            && self.uintv.ord(&other.uintv)
            && self.floatv.ord(&other.floatv)
            && self.boolv.ord(&other.boolv)
            && self.listv.ord(&other.listv)
            && self.ptrv.ord(&other.ptrv)
            && self.adtv.ord(&other.adtv)
            && self.optionv.ord(&other.optionv)
            && self.fnv.ord(&other.fnv)
    }

    pub fn int_top() -> Self {
        Self {
            intv: AbsInt::top(),
            ..Self::bot()
        }
    }

    pub fn uint_top() -> Self {
        Self {
            uintv: AbsUint::top(),
            ..Self::bot()
        }
    }

    pub fn float_top() -> Self {
        Self {
            floatv: AbsFloat::top(),
            ..Self::bot()
        }
    }

    pub fn bool_top() -> Self {
        Self {
            boolv: AbsBool::top(),
            ..Self::bot()
        }
    }

    pub fn int(n: i128) -> Self {
        Self {
            intv: AbsInt::alpha(n),
            ..Self::bot()
        }
    }

    pub fn uint(n: u128) -> Self {
        Self {
            uintv: AbsUint::alpha(n),
            ..Self::bot()
        }
    }

    pub fn float(f: f64) -> Self {
        Self {
            floatv: AbsFloat::alpha(f),
            ..Self::bot()
        }
    }

    pub fn list(l: Vec<AbsValue>) -> Self {
        Self {
            listv: AbsList::List(l),
            ..Self::bot()
        }
    }

    pub fn not(&self) -> Self {
        Self {
            intv: self.intv.not(),
            uintv: self.uintv.not(),
            boolv: self.boolv.not(),
            ..Self::bot()
        }
    }

    pub fn neg(&self) -> Self {
        Self {
            intv: self.intv.neg(),
            floatv: self.floatv.neg(),
            ..Self::bot()
        }
    }

    pub fn to_i8(&self) -> Self {
        Self {
            intv: self
                .intv
                .to_i8()
                .join(&self.uintv.to_i8())
                .join(&self.floatv.to_i8()),
            ..Self::bot()
        }
    }

    pub fn to_i16(&self) -> Self {
        Self {
            intv: self
                .intv
                .to_i16()
                .join(&self.uintv.to_i16())
                .join(&self.floatv.to_i16()),
            ..Self::bot()
        }
    }

    pub fn to_i32(&self) -> Self {
        Self {
            intv: self
                .intv
                .to_i32()
                .join(&self.uintv.to_i32())
                .join(&self.floatv.to_i32()),
            ..Self::bot()
        }
    }

    pub fn to_i64(&self) -> Self {
        Self {
            intv: self
                .intv
                .to_i64()
                .join(&self.uintv.to_i64())
                .join(&self.floatv.to_i64()),
            ..Self::bot()
        }
    }

    pub fn to_i128(&self) -> Self {
        Self {
            intv: self
                .intv
                .join(&self.uintv.to_i128())
                .join(&self.floatv.to_i128()),
            ..Self::bot()
        }
    }

    pub fn to_u8(&self) -> Self {
        Self {
            uintv: self
                .intv
                .to_u8()
                .join(&self.uintv.to_u8())
                .join(&self.floatv.to_u8()),
            ..Self::bot()
        }
    }

    pub fn to_u16(&self) -> Self {
        Self {
            uintv: self
                .intv
                .to_u16()
                .join(&self.uintv.to_u16())
                .join(&self.floatv.to_u16()),
            ..Self::bot()
        }
    }

    pub fn to_u32(&self) -> Self {
        Self {
            uintv: self
                .intv
                .to_u32()
                .join(&self.uintv.to_u32())
                .join(&self.floatv.to_u32()),
            ..Self::bot()
        }
    }

    pub fn to_u64(&self) -> Self {
        Self {
            uintv: self
                .intv
                .to_u64()
                .join(&self.uintv.to_u64())
                .join(&self.floatv.to_u64()),
            ..Self::bot()
        }
    }

    pub fn to_u128(&self) -> Self {
        Self {
            uintv: self
                .intv
                .to_u128()
                .join(&self.uintv)
                .join(&self.floatv.to_u128()),
            ..Self::bot()
        }
    }

    pub fn to_f32(&self) -> Self {
        Self {
            floatv: self
                .intv
                .to_f32()
                .join(&self.uintv.to_f32())
                .join(&self.floatv.to_f32()),
            ..Self::bot()
        }
    }

    pub fn to_f64(&self) -> Self {
        Self {
            floatv: self
                .intv
                .to_f64()
                .join(&self.uintv.to_f64())
                .join(&self.floatv),
            ..Self::bot()
        }
    }

    pub fn add(&self, other: &Self) -> Self {
        Self {
            intv: self.intv.add(&other.intv),
            uintv: self.uintv.add(&other.uintv),
            floatv: self.floatv.add(&other.floatv),
            ..Self::bot()
        }
    }

    pub fn sub(&self, other: &Self) -> Self {
        Self {
            intv: self.intv.sub(&other.intv),
            uintv: self.uintv.sub(&other.uintv),
            floatv: self.floatv.sub(&other.floatv),
            ..Self::bot()
        }
    }

    pub fn mul(&self, other: &Self) -> Self {
        Self {
            intv: self.intv.mul(&other.intv),
            uintv: self.uintv.mul(&other.uintv),
            floatv: self.floatv.mul(&other.floatv),
            ..Self::bot()
        }
    }

    pub fn div(&self, other: &Self) -> Self {
        Self {
            intv: self.intv.div(&other.intv),
            uintv: self.uintv.div(&other.uintv),
            floatv: self.floatv.div(&other.floatv),
            ..Self::bot()
        }
    }

    pub fn rem(&self, other: &Self) -> Self {
        Self {
            intv: self.intv.rem(&other.intv),
            uintv: self.uintv.rem(&other.uintv),
            floatv: self.floatv.rem(&other.floatv),
            ..Self::bot()
        }
    }

    pub fn bit_xor(&self, other: &Self) -> Self {
        Self {
            intv: self.intv.bit_xor(&other.intv),
            uintv: self.uintv.bit_xor(&other.uintv),
            boolv: self.boolv.bit_xor(&other.boolv),
            ..Self::bot()
        }
    }

    pub fn bit_and(&self, other: &Self) -> Self {
        Self {
            intv: self.intv.bit_and(&other.intv),
            uintv: self.uintv.bit_and(&other.uintv),
            boolv: self.boolv.bit_and(&other.boolv),
            ..Self::bot()
        }
    }

    pub fn bit_or(&self, other: &Self) -> Self {
        Self {
            intv: self.intv.bit_or(&other.intv),
            uintv: self.uintv.bit_or(&other.uintv),
            boolv: self.boolv.bit_or(&other.boolv),
            ..Self::bot()
        }
    }

    pub fn shl(&self, other: &Self) -> Self {
        Self {
            intv: self
                .intv
                .shl(&other.intv)
                .join(&self.intv.shlu(&other.uintv)),
            uintv: self
                .uintv
                .shl(&other.uintv)
                .join(&self.uintv.shli(&other.intv)),
            ..Self::bot()
        }
    }

    pub fn shr(&self, other: &Self) -> Self {
        Self {
            intv: self
                .intv
                .shr(&other.intv)
                .join(&self.intv.shru(&other.uintv)),
            uintv: self
                .uintv
                .shr(&other.uintv)
                .join(&self.uintv.shri(&other.intv)),
            ..Self::bot()
        }
    }

    pub fn eq(&self, other: &Self) -> Self {
        Self {
            boolv: self
                .intv
                .eq(&other.intv)
                .join(&self.uintv.eq(&other.uintv))
                .join(&self.floatv.eq(&other.floatv))
                .join(&self.boolv.eq(&other.boolv)),
            ..Self::bot()
        }
    }

    pub fn lt(&self, other: &Self) -> Self {
        Self {
            boolv: self
                .intv
                .lt(&other.intv)
                .join(&self.uintv.lt(&other.uintv))
                .join(&self.floatv.lt(&other.floatv)),
            ..Self::bot()
        }
    }

    pub fn le(&self, other: &Self) -> Self {
        Self {
            boolv: self
                .intv
                .le(&other.intv)
                .join(&self.uintv.le(&other.uintv))
                .join(&self.floatv.le(&other.floatv)),
            ..Self::bot()
        }
    }

    pub fn ne(&self, other: &Self) -> Self {
        Self {
            boolv: self
                .intv
                .ne(&other.intv)
                .join(&self.uintv.ne(&other.uintv))
                .join(&self.floatv.ne(&other.floatv))
                .join(&self.boolv.ne(&other.boolv)),
            ..Self::bot()
        }
    }

    pub fn ge(&self, other: &Self) -> Self {
        Self {
            boolv: self
                .intv
                .ge(&other.intv)
                .join(&self.uintv.ge(&other.uintv))
                .join(&self.floatv.ge(&other.floatv)),
            ..Self::bot()
        }
    }

    pub fn gt(&self, other: &Self) -> Self {
        Self {
            boolv: self
                .intv
                .gt(&other.intv)
                .join(&self.uintv.gt(&other.uintv))
                .join(&self.floatv.gt(&other.floatv)),
            ..Self::bot()
        }
    }
}

const MAX_SIZE: usize = 10;

#[derive(Clone)]
pub enum AbsInt {
    Top,
    Set(BTreeSet<i128>),
}

impl std::fmt::Debug for AbsInt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Top => write!(f, "Top_i"),
            Self::Set(s) => match s.len() {
                0 => write!(f, "Bot_i"),
                1 => write!(f, "{}_i", s.first().unwrap()),
                _ => {
                    write!(f, "{{")?;
                    for (i, n) in s.iter().enumerate() {
                        if i != 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", n)?;
                    }
                    write!(f, "}}_i")
                }
            },
        }
    }
}

impl AbsInt {
    pub fn top() -> Self {
        Self::Top
    }

    pub fn bot() -> Self {
        Self::alphas(BTreeSet::new())
    }

    pub fn is_bot(&self) -> bool {
        if let Self::Set(s) = self {
            s.is_empty()
        } else {
            false
        }
    }

    pub fn alpha(n: i128) -> Self {
        Self::alphas([n].into_iter().collect())
    }

    pub fn alphas(set: BTreeSet<i128>) -> Self {
        if set.len() > MAX_SIZE {
            Self::Top
        } else {
            Self::Set(set)
        }
    }

    pub fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Top, _) | (_, Self::Top) => Self::Top,
            (Self::Set(s1), Self::Set(s2)) => Self::alphas(s1.union(s2).cloned().collect()),
        }
    }

    pub fn ord(&self, other: &Self) -> bool {
        match (self, other) {
            (_, Self::Top) => true,
            (Self::Top, _) => false,
            (Self::Set(s1), Self::Set(s2)) => s1.is_subset(s2),
        }
    }

    fn unary<F: Fn(i128) -> i128>(&self, f: F) -> Self {
        match self {
            Self::Top => Self::Top,
            Self::Set(s) => Self::alphas(s.iter().map(|n| f(*n)).collect()),
        }
    }

    pub fn not(&self) -> Self {
        self.unary(|n| !n)
    }

    pub fn neg(&self) -> Self {
        self.unary(|n| -n)
    }

    pub fn to_i8(&self) -> Self {
        self.unary(|n| n as i8 as i128)
    }

    pub fn to_i16(&self) -> Self {
        self.unary(|n| n as i16 as i128)
    }

    pub fn to_i32(&self) -> Self {
        self.unary(|n| n as i32 as i128)
    }

    pub fn to_i64(&self) -> Self {
        self.unary(|n| n as i64 as i128)
    }

    fn unaryu<F: Fn(i128) -> u128>(&self, f: F) -> AbsUint {
        match self {
            Self::Top => AbsUint::Top,
            Self::Set(s) => AbsUint::alphas(s.iter().map(|n| f(*n)).collect()),
        }
    }

    pub fn to_u8(&self) -> AbsUint {
        self.unaryu(|n| n as u8 as u128)
    }

    pub fn to_u16(&self) -> AbsUint {
        self.unaryu(|n| n as u16 as u128)
    }

    pub fn to_u32(&self) -> AbsUint {
        self.unaryu(|n| n as u32 as u128)
    }

    pub fn to_u64(&self) -> AbsUint {
        self.unaryu(|n| n as u64 as u128)
    }

    pub fn to_u128(&self) -> AbsUint {
        self.unaryu(|n| n as u128)
    }

    fn unaryf<F: Fn(i128) -> f64>(&self, f: F) -> AbsFloat {
        match self {
            Self::Top => AbsFloat::Top,
            Self::Set(s) => AbsFloat::alphas(s.iter().map(|n| f(*n)).collect()),
        }
    }

    pub fn to_f32(&self) -> AbsFloat {
        self.unaryf(|n| n as f32 as f64)
    }

    pub fn to_f64(&self) -> AbsFloat {
        self.unaryf(|n| n as f64)
    }

    fn binary<F: Fn(i128, i128) -> i128>(&self, other: &Self, f: F) -> Self {
        match (self, other) {
            (Self::Top, _) | (_, Self::Top) => Self::Top,
            (Self::Set(s1), Self::Set(s2)) => {
                let mut set = BTreeSet::new();
                for n1 in s1 {
                    for n2 in s2 {
                        set.insert(f(*n1, *n2));
                    }
                }
                Self::alphas(set)
            }
        }
    }

    pub fn add(&self, other: &Self) -> Self {
        self.binary(other, |n1, n2| n1 + n2)
    }

    pub fn sub(&self, other: &Self) -> Self {
        self.binary(other, |n1, n2| n1 - n2)
    }

    pub fn mul(&self, other: &Self) -> Self {
        self.binary(other, |n1, n2| n1 * n2)
    }

    pub fn div(&self, other: &Self) -> Self {
        self.binary(other, |n1, n2| n1 / n2)
    }

    pub fn rem(&self, other: &Self) -> Self {
        self.binary(other, |n1, n2| n1 % n2)
    }

    pub fn bit_xor(&self, other: &Self) -> Self {
        self.binary(other, |n1, n2| n1 ^ n2)
    }

    pub fn bit_and(&self, other: &Self) -> Self {
        self.binary(other, |n1, n2| n1 & n2)
    }

    pub fn bit_or(&self, other: &Self) -> Self {
        self.binary(other, |n1, n2| n1 | n2)
    }

    pub fn shl(&self, other: &Self) -> Self {
        self.binary(other, |n1, n2| n1 << n2)
    }

    pub fn shr(&self, other: &Self) -> Self {
        self.binary(other, |n1, n2| n1 >> n2)
    }

    fn binaryu<F: Fn(i128, u128) -> i128>(&self, other: &AbsUint, f: F) -> Self {
        match (self, other) {
            (Self::Top, _) | (_, AbsUint::Top) => Self::Top,
            (Self::Set(s1), AbsUint::Set(s2)) => {
                let mut set = BTreeSet::new();
                for n1 in s1 {
                    for n2 in s2 {
                        set.insert(f(*n1, *n2));
                    }
                }
                Self::alphas(set)
            }
        }
    }

    pub fn shlu(&self, other: &AbsUint) -> Self {
        self.binaryu(other, |n1, n2| n1 << n2)
    }

    pub fn shru(&self, other: &AbsUint) -> Self {
        self.binaryu(other, |n1, n2| n1 >> n2)
    }

    fn binaryb<F: Fn(i128, i128) -> bool>(&self, other: &Self, f: F) -> AbsBool {
        match (self, other) {
            (Self::Top, _) | (_, Self::Top) => AbsBool::Top,
            (Self::Set(s1), Self::Set(s2)) => {
                let mut set = BTreeSet::new();
                for n1 in s1 {
                    for n2 in s2 {
                        set.insert(f(*n1, *n2));
                    }
                }
                AbsBool::alphas(set)
            }
        }
    }

    pub fn eq(&self, other: &Self) -> AbsBool {
        self.binaryb(other, |n1, n2| n1 == n2)
    }

    pub fn lt(&self, other: &Self) -> AbsBool {
        self.binaryb(other, |n1, n2| n1 < n2)
    }

    pub fn le(&self, other: &Self) -> AbsBool {
        self.binaryb(other, |n1, n2| n1 <= n2)
    }

    pub fn ne(&self, other: &Self) -> AbsBool {
        self.binaryb(other, |n1, n2| n1 != n2)
    }

    pub fn ge(&self, other: &Self) -> AbsBool {
        self.binaryb(other, |n1, n2| n1 >= n2)
    }

    pub fn gt(&self, other: &Self) -> AbsBool {
        self.binaryb(other, |n1, n2| n1 > n2)
    }
}

#[derive(Clone)]
pub enum AbsUint {
    Top,
    Set(BTreeSet<u128>),
}

impl std::fmt::Debug for AbsUint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Top => write!(f, "Top_u"),
            Self::Set(s) => match s.len() {
                0 => write!(f, "Bot_u"),
                1 => write!(f, "{}_u", s.first().unwrap()),
                _ => {
                    write!(f, "{{")?;
                    for (i, n) in s.iter().enumerate() {
                        if i != 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", n)?;
                    }
                    write!(f, "}}_u")
                }
            },
        }
    }
}

impl AbsUint {
    pub fn top() -> Self {
        Self::Top
    }

    pub fn bot() -> Self {
        Self::alphas(BTreeSet::new())
    }

    pub fn is_bot(&self) -> bool {
        if let Self::Set(s) = self {
            s.is_empty()
        } else {
            false
        }
    }

    pub fn alpha(n: u128) -> Self {
        Self::alphas([n].into_iter().collect())
    }

    pub fn alphas(set: BTreeSet<u128>) -> Self {
        if set.len() > MAX_SIZE {
            Self::Top
        } else {
            Self::Set(set)
        }
    }

    pub fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Top, _) | (_, Self::Top) => Self::Top,
            (Self::Set(s1), Self::Set(s2)) => Self::alphas(s1.union(s2).cloned().collect()),
        }
    }

    pub fn ord(&self, other: &Self) -> bool {
        match (self, other) {
            (_, Self::Top) => true,
            (Self::Top, _) => false,
            (Self::Set(s1), Self::Set(s2)) => s1.is_subset(s2),
        }
    }

    fn unary<F: Fn(u128) -> u128>(&self, f: F) -> Self {
        match self {
            Self::Top => Self::Top,
            Self::Set(s) => Self::alphas(s.iter().map(|n| f(*n)).collect()),
        }
    }

    pub fn not(&self) -> Self {
        self.unary(|n| !n)
    }

    pub fn to_u8(&self) -> Self {
        self.unary(|n| n as u8 as u128)
    }

    pub fn to_u16(&self) -> Self {
        self.unary(|n| n as u16 as u128)
    }

    pub fn to_u32(&self) -> Self {
        self.unary(|n| n as u32 as u128)
    }

    pub fn to_u64(&self) -> Self {
        self.unary(|n| n as u64 as u128)
    }

    fn unaryi<F: Fn(u128) -> i128>(&self, f: F) -> AbsInt {
        match self {
            Self::Top => AbsInt::Top,
            Self::Set(s) => AbsInt::alphas(s.iter().map(|n| f(*n)).collect()),
        }
    }

    pub fn to_i8(&self) -> AbsInt {
        self.unaryi(|n| n as i8 as i128)
    }

    pub fn to_i16(&self) -> AbsInt {
        self.unaryi(|n| n as i16 as i128)
    }

    pub fn to_i32(&self) -> AbsInt {
        self.unaryi(|n| n as i32 as i128)
    }

    pub fn to_i64(&self) -> AbsInt {
        self.unaryi(|n| n as i64 as i128)
    }

    pub fn to_i128(&self) -> AbsInt {
        self.unaryi(|n| n as i128)
    }

    fn unaryf<F: Fn(u128) -> f64>(&self, f: F) -> AbsFloat {
        match self {
            Self::Top => AbsFloat::Top,
            Self::Set(s) => AbsFloat::alphas(s.iter().map(|n| f(*n)).collect()),
        }
    }

    pub fn to_f32(&self) -> AbsFloat {
        self.unaryf(|n| n as f32 as f64)
    }

    pub fn to_f64(&self) -> AbsFloat {
        self.unaryf(|n| n as f64)
    }

    fn binary<F: Fn(u128, u128) -> u128>(&self, other: &Self, f: F) -> Self {
        match (self, other) {
            (Self::Top, _) | (_, Self::Top) => Self::Top,
            (Self::Set(s1), Self::Set(s2)) => {
                let mut set = BTreeSet::new();
                for n1 in s1 {
                    for n2 in s2 {
                        set.insert(f(*n1, *n2));
                    }
                }
                Self::alphas(set)
            }
        }
    }

    pub fn add(&self, other: &Self) -> Self {
        self.binary(other, |n1, n2| n1 + n2)
    }

    pub fn sub(&self, other: &Self) -> Self {
        self.binary(other, |n1, n2| n1 - n2)
    }

    pub fn mul(&self, other: &Self) -> Self {
        self.binary(other, |n1, n2| n1 * n2)
    }

    pub fn div(&self, other: &Self) -> Self {
        self.binary(other, |n1, n2| n1 / n2)
    }

    pub fn rem(&self, other: &Self) -> Self {
        self.binary(other, |n1, n2| n1 % n2)
    }

    pub fn bit_xor(&self, other: &Self) -> Self {
        self.binary(other, |n1, n2| n1 ^ n2)
    }

    pub fn bit_and(&self, other: &Self) -> Self {
        self.binary(other, |n1, n2| n1 & n2)
    }

    pub fn bit_or(&self, other: &Self) -> Self {
        self.binary(other, |n1, n2| n1 | n2)
    }

    pub fn shl(&self, other: &Self) -> Self {
        self.binary(other, |n1, n2| n1 << n2)
    }

    pub fn shr(&self, other: &Self) -> Self {
        self.binary(other, |n1, n2| n1 >> n2)
    }

    fn binaryi<F: Fn(u128, i128) -> u128>(&self, other: &AbsInt, f: F) -> Self {
        match (self, other) {
            (Self::Top, _) | (_, AbsInt::Top) => Self::Top,
            (Self::Set(s1), AbsInt::Set(s2)) => {
                let mut set = BTreeSet::new();
                for n1 in s1 {
                    for n2 in s2 {
                        set.insert(f(*n1, *n2));
                    }
                }
                Self::alphas(set)
            }
        }
    }

    pub fn shli(&self, other: &AbsInt) -> Self {
        self.binaryi(other, |n1, n2| n1 << n2)
    }

    pub fn shri(&self, other: &AbsInt) -> Self {
        self.binaryi(other, |n1, n2| n1 >> n2)
    }

    fn binaryb<F: Fn(u128, u128) -> bool>(&self, other: &Self, f: F) -> AbsBool {
        match (self, other) {
            (Self::Top, _) | (_, Self::Top) => AbsBool::Top,
            (Self::Set(s1), Self::Set(s2)) => {
                let mut set = BTreeSet::new();
                for n1 in s1 {
                    for n2 in s2 {
                        set.insert(f(*n1, *n2));
                    }
                }
                AbsBool::alphas(set)
            }
        }
    }

    pub fn eq(&self, other: &Self) -> AbsBool {
        self.binaryb(other, |n1, n2| n1 == n2)
    }

    pub fn lt(&self, other: &Self) -> AbsBool {
        self.binaryb(other, |n1, n2| n1 < n2)
    }

    pub fn le(&self, other: &Self) -> AbsBool {
        self.binaryb(other, |n1, n2| n1 <= n2)
    }

    pub fn ne(&self, other: &Self) -> AbsBool {
        self.binaryb(other, |n1, n2| n1 != n2)
    }

    pub fn ge(&self, other: &Self) -> AbsBool {
        self.binaryb(other, |n1, n2| n1 >= n2)
    }

    pub fn gt(&self, other: &Self) -> AbsBool {
        self.binaryb(other, |n1, n2| n1 > n2)
    }
}

#[derive(Clone)]
pub enum AbsFloat {
    Top,
    Set(BTreeSet<u64>),
}

impl std::fmt::Debug for AbsFloat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Top => write!(f, "Top_f"),
            Self::Set(s) => match s.len() {
                0 => write!(f, "Bot_f"),
                1 => write!(f, "{}_f", f64::from_bits(*s.first().unwrap())),
                _ => {
                    write!(f, "{{")?;
                    for (i, n) in s.iter().enumerate() {
                        if i != 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", f64::from_bits(*n))?;
                    }
                    write!(f, "}}_f")
                }
            },
        }
    }
}

impl AbsFloat {
    pub fn top() -> Self {
        Self::Top
    }

    fn new(set: BTreeSet<u64>) -> Self {
        if set.len() > MAX_SIZE {
            Self::Top
        } else {
            Self::Set(set)
        }
    }

    pub fn bot() -> Self {
        Self::new(BTreeSet::new())
    }

    pub fn is_bot(&self) -> bool {
        if let Self::Set(s) = self {
            s.is_empty()
        } else {
            false
        }
    }

    pub fn alpha(n: f64) -> Self {
        Self::new([n.to_bits()].into_iter().collect())
    }

    pub fn alphas(v: Vec<f64>) -> Self {
        Self::new(v.into_iter().map(|n| n.to_bits()).collect())
    }

    pub fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Top, _) | (_, Self::Top) => Self::Top,
            (Self::Set(s1), Self::Set(s2)) => Self::new(s1.union(s2).cloned().collect()),
        }
    }

    pub fn ord(&self, other: &Self) -> bool {
        match (self, other) {
            (_, Self::Top) => true,
            (Self::Top, _) => false,
            (Self::Set(s1), Self::Set(s2)) => s1.is_subset(s2),
        }
    }

    fn unary<F: Fn(f64) -> f64>(&self, f: F) -> Self {
        match self {
            Self::Top => Self::Top,
            Self::Set(s) => Self::new(s.iter().map(|n| f(f64::from_bits(*n)).to_bits()).collect()),
        }
    }

    pub fn neg(&self) -> Self {
        self.unary(|n| -n)
    }

    pub fn to_f32(&self) -> Self {
        self.unary(|n| n as f32 as f64)
    }

    fn unaryi<F: Fn(f64) -> i128>(&self, f: F) -> AbsInt {
        match self {
            Self::Top => AbsInt::Top,
            Self::Set(s) => AbsInt::alphas(s.iter().map(|n| f(f64::from_bits(*n))).collect()),
        }
    }

    pub fn to_i8(&self) -> AbsInt {
        self.unaryi(|n| n as i8 as i128)
    }

    pub fn to_i16(&self) -> AbsInt {
        self.unaryi(|n| n as i16 as i128)
    }

    pub fn to_i32(&self) -> AbsInt {
        self.unaryi(|n| n as i32 as i128)
    }

    pub fn to_i64(&self) -> AbsInt {
        self.unaryi(|n| n as i64 as i128)
    }

    pub fn to_i128(&self) -> AbsInt {
        self.unaryi(|n| n as i128)
    }

    fn unaryu<F: Fn(f64) -> u128>(&self, f: F) -> AbsUint {
        match self {
            Self::Top => AbsUint::Top,
            Self::Set(s) => AbsUint::alphas(s.iter().map(|n| f(f64::from_bits(*n))).collect()),
        }
    }

    pub fn to_u8(&self) -> AbsUint {
        self.unaryu(|n| n as u8 as u128)
    }

    pub fn to_u16(&self) -> AbsUint {
        self.unaryu(|n| n as u16 as u128)
    }

    pub fn to_u32(&self) -> AbsUint {
        self.unaryu(|n| n as u32 as u128)
    }

    pub fn to_u64(&self) -> AbsUint {
        self.unaryu(|n| n as u64 as u128)
    }

    pub fn to_u128(&self) -> AbsUint {
        self.unaryu(|n| n as u128)
    }

    fn binary<F: Fn(f64, f64) -> f64>(&self, other: &Self, f: F) -> Self {
        match (self, other) {
            (Self::Top, _) | (_, Self::Top) => Self::Top,
            (Self::Set(s1), Self::Set(s2)) => {
                let mut set = BTreeSet::new();
                for n1 in s1 {
                    for n2 in s2 {
                        set.insert(f(f64::from_bits(*n1), f64::from_bits(*n2)).to_bits());
                    }
                }
                Self::new(set)
            }
        }
    }

    pub fn add(&self, other: &Self) -> Self {
        self.binary(other, |n1, n2| n1 + n2)
    }

    pub fn sub(&self, other: &Self) -> Self {
        self.binary(other, |n1, n2| n1 - n2)
    }

    pub fn mul(&self, other: &Self) -> Self {
        self.binary(other, |n1, n2| n1 * n2)
    }

    pub fn div(&self, other: &Self) -> Self {
        self.binary(other, |n1, n2| n1 / n2)
    }

    pub fn rem(&self, other: &Self) -> Self {
        self.binary(other, |n1, n2| n1 % n2)
    }

    fn binaryb<F: Fn(f64, f64) -> bool>(&self, other: &Self, f: F) -> AbsBool {
        match (self, other) {
            (Self::Top, _) | (_, Self::Top) => AbsBool::Top,
            (Self::Set(s1), Self::Set(s2)) => {
                let mut set = BTreeSet::new();
                for n1 in s1 {
                    for n2 in s2 {
                        set.insert(f(f64::from_bits(*n1), f64::from_bits(*n2)));
                    }
                }
                AbsBool::alphas(set)
            }
        }
    }

    pub fn eq(&self, other: &Self) -> AbsBool {
        self.binaryb(other, |n1, n2| n1 == n2)
    }

    pub fn lt(&self, other: &Self) -> AbsBool {
        self.binaryb(other, |n1, n2| n1 < n2)
    }

    pub fn le(&self, other: &Self) -> AbsBool {
        self.binaryb(other, |n1, n2| n1 <= n2)
    }

    pub fn ne(&self, other: &Self) -> AbsBool {
        self.binaryb(other, |n1, n2| n1 != n2)
    }

    pub fn ge(&self, other: &Self) -> AbsBool {
        self.binaryb(other, |n1, n2| n1 >= n2)
    }

    pub fn gt(&self, other: &Self) -> AbsBool {
        self.binaryb(other, |n1, n2| n1 > n2)
    }
}

#[derive(Clone, Copy)]
pub enum AbsBool {
    Top,
    True,
    False,
    Bot,
}

impl std::fmt::Debug for AbsBool {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AbsBool::Top => write!(f, "Top_b"),
            AbsBool::True => write!(f, "true"),
            AbsBool::False => write!(f, "false"),
            AbsBool::Bot => write!(f, "Bot_b"),
        }
    }
}

impl AbsBool {
    pub fn top() -> Self {
        Self::Top
    }

    pub fn bot() -> Self {
        Self::Bot
    }

    pub fn is_bot(&self) -> bool {
        matches!(self, Self::Bot)
    }

    pub fn alpha(b: bool) -> Self {
        if b {
            Self::True
        } else {
            Self::False
        }
    }

    pub fn alphas(set: BTreeSet<bool>) -> Self {
        if set.len() == 2 {
            Self::Top
        } else if set.contains(&true) {
            Self::True
        } else if set.contains(&false) {
            Self::False
        } else {
            Self::Bot
        }
    }

    pub fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::True, Self::True) => Self::True,
            (Self::False, Self::False) => Self::False,
            (Self::Bot, v) | (v, Self::Bot) => *v,
            _ => Self::Top,
        }
    }

    pub fn ord(&self, other: &Self) -> bool {
        matches!(
            (self, other),
            (_, Self::Top) | (Self::Bot, _) | (Self::True, Self::True) | (Self::False, Self::False)
        )
    }

    pub fn not(&self) -> Self {
        match self {
            Self::Top => Self::Top,
            Self::True => Self::False,
            Self::False => Self::True,
            Self::Bot => Self::Bot,
        }
    }

    pub fn eq(&self, other: &Self) -> AbsBool {
        match (self, other) {
            (Self::Bot, _) | (_, Self::Bot) => Self::Bot,
            (Self::True, Self::True) | (Self::False, Self::False) => Self::True,
            (Self::True, Self::False) | (Self::False, Self::True) => Self::False,
            _ => Self::Top,
        }
    }

    pub fn ne(&self, other: &Self) -> AbsBool {
        match (self, other) {
            (Self::Bot, _) | (_, Self::Bot) => Self::Bot,
            (Self::True, Self::True) | (Self::False, Self::False) => Self::False,
            (Self::True, Self::False) | (Self::False, Self::True) => Self::True,
            _ => Self::Top,
        }
    }

    pub fn bit_xor(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Bot, _) | (_, Self::Bot) => Self::Bot,
            (Self::True, Self::True) | (Self::False, Self::False) => Self::False,
            (Self::True, Self::False) | (Self::False, Self::True) => Self::True,
            _ => Self::Top,
        }
    }

    pub fn bit_and(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Bot, _) | (_, Self::Bot) => Self::Bot,
            (Self::True, _) | (_, Self::True) => Self::True,
            (Self::False, Self::False) => Self::False,
            _ => Self::Top,
        }
    }

    pub fn bit_or(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Bot, _) | (_, Self::Bot) => Self::Bot,
            (Self::False, _) | (_, Self::False) => Self::False,
            (Self::True, Self::True) => Self::True,
            _ => Self::Top,
        }
    }
}

#[derive(Debug, Clone)]
pub enum AbsList {
    Top,
    List(Vec<AbsValue>),
    Bot,
}

impl AbsList {
    pub fn top() -> Self {
        Self::Top
    }

    pub fn bot() -> Self {
        Self::Bot
    }

    pub fn is_bot(&self) -> bool {
        matches!(self, Self::Bot)
    }

    pub fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Bot, v) | (v, Self::Bot) => v.clone(),
            (Self::List(l1), Self::List(l2)) if l1.len() == l2.len() => Self::List(
                l1.iter()
                    .zip(l2.iter())
                    .map(|(v1, v2)| v1.join(v2))
                    .collect(),
            ),
            _ => Self::Top,
        }
    }

    pub fn ord(&self, other: &Self) -> bool {
        match (self, other) {
            (_, Self::Top) | (Self::Bot, _) => true,
            (Self::List(l1), Self::List(l2)) if l1.len() == l2.len() => {
                l1.iter().zip(l2.iter()).all(|(v1, v2)| v1.ord(v2))
            }
            _ => false,
        }
    }
}

#[derive(Debug, Clone)]
pub enum AbsPtr {
    Top,
    Set(BTreeSet<usize>),
}

impl AbsPtr {
    pub fn top() -> Self {
        Self::Top
    }

    pub fn bot() -> Self {
        Self::Set(BTreeSet::new())
    }

    pub fn is_bot(&self) -> bool {
        if let Self::Set(s) = self {
            s.is_empty()
        } else {
            false
        }
    }

    pub fn alpha(n: usize) -> Self {
        Self::alphas([n].into_iter().collect())
    }

    pub fn alphas(set: BTreeSet<usize>) -> Self {
        if set.len() > MAX_SIZE {
            Self::Top
        } else {
            Self::Set(set)
        }
    }

    pub fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Top, _) | (_, Self::Top) => Self::Top,
            (Self::Set(s1), Self::Set(s2)) => Self::alphas(s1.union(s2).cloned().collect()),
        }
    }

    pub fn ord(&self, other: &Self) -> bool {
        match (self, other) {
            (_, Self::Top) => true,
            (Self::Top, _) => false,
            (Self::Set(s1), Self::Set(s2)) => s1.is_subset(s2),
        }
    }
}

#[derive(Debug, Clone)]
pub enum AbsAdt {
    Top,
    Map(BTreeMap<FieldIdx, AbsValue>),
    Bot,
}

impl AbsAdt {
    pub fn top() -> Self {
        Self::Top
    }

    pub fn bot() -> Self {
        Self::Bot
    }

    pub fn is_bot(&self) -> bool {
        matches!(self, Self::Bot)
    }

    pub fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Bot, v) | (v, Self::Bot) => v.clone(),
            (Self::Map(l1), Self::Map(l2))
                if l1.keys().all(|k| l2.contains_key(k))
                    && l2.keys().all(|k| l1.contains_key(k)) =>
            {
                Self::Map(l1.keys().map(|k| (*k, l1[k].join(&l2[k]))).collect())
            }
            _ => Self::Top,
        }
    }

    pub fn ord(&self, other: &Self) -> bool {
        match (self, other) {
            (_, Self::Top) | (Self::Bot, _) => true,
            (Self::Map(l1), Self::Map(l2))
                if l1.keys().all(|k| l2.contains_key(k))
                    && l2.keys().all(|k| l1.contains_key(k)) =>
            {
                l1.keys().all(|k| l1[k].ord(&l2[k]))
            }
            _ => false,
        }
    }
}

#[derive(Debug, Clone)]
pub enum AbsOption {
    Top,
    Some(Box<AbsValue>),
    None,
    Bot,
}

impl AbsOption {
    pub fn top() -> Self {
        Self::Top
    }

    pub fn bot() -> Self {
        Self::Bot
    }

    pub fn is_bot(&self) -> bool {
        matches!(self, Self::Bot)
    }

    pub fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Bot, v) | (v, Self::Bot) => v.clone(),
            (Self::None, Self::None) => Self::None,
            (Self::Some(v1), Self::Some(v2)) => Self::Some(Box::new(v1.join(v2))),
            _ => Self::Top,
        }
    }

    pub fn ord(&self, other: &Self) -> bool {
        match (self, other) {
            (_, Self::Top) | (Self::Bot, _) | (Self::None, Self::None) => true,
            (Self::Some(v1), Self::Some(v2)) => v1.ord(v2),
            _ => false,
        }
    }
}

#[derive(Debug, Clone)]
pub enum AbsFn {
    Top,
    Set(BTreeSet<DefId>),
}

impl AbsFn {
    pub fn top() -> Self {
        Self::Top
    }

    pub fn bot() -> Self {
        Self::Set(BTreeSet::new())
    }

    pub fn is_bot(&self) -> bool {
        if let Self::Set(s) = self {
            s.is_empty()
        } else {
            false
        }
    }

    pub fn alpha(n: DefId) -> Self {
        Self::alphas([n].into_iter().collect())
    }

    pub fn alphas(set: BTreeSet<DefId>) -> Self {
        if set.len() > MAX_SIZE {
            Self::Top
        } else {
            Self::Set(set)
        }
    }

    pub fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Top, _) | (_, Self::Top) => Self::Top,
            (Self::Set(s1), Self::Set(s2)) => Self::alphas(s1.union(s2).cloned().collect()),
        }
    }

    pub fn ord(&self, other: &Self) -> bool {
        match (self, other) {
            (_, Self::Top) => true,
            (Self::Top, _) => false,
            (Self::Set(s1), Self::Set(s2)) => s1.is_subset(s2),
        }
    }
}
