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
pub struct AbsLocal(pub Vec<AbsValue>);

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
}

#[derive(Debug, Clone)]
pub struct AbsValue {
    pub intv: AbsInt,
    pub uintv: AbsUint,
    pub boolv: AbsBool,
    pub listv: AbsList,
    pub ptrv: AbsPtr,
    pub adtv: AbsAdt,
    pub optionv: AbsOption,
    pub fnv: AbsFn,
}

impl AbsValue {
    pub fn top() -> Self {
        Self {
            intv: AbsInt::top(),
            uintv: AbsUint::top(),
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
            && self.boolv.ord(&other.boolv)
            && self.listv.ord(&other.listv)
            && self.ptrv.ord(&other.ptrv)
            && self.adtv.ord(&other.adtv)
            && self.optionv.ord(&other.optionv)
            && self.fnv.ord(&other.fnv)
    }

    pub fn int(n: i128) -> Self {
        Self {
            intv: AbsInt::alpha(n),
            uintv: AbsUint::bot(),
            boolv: AbsBool::bot(),
            listv: AbsList::bot(),
            ptrv: AbsPtr::bot(),
            adtv: AbsAdt::bot(),
            optionv: AbsOption::bot(),
            fnv: AbsFn::bot(),
        }
    }

    pub fn uint(n: u128) -> Self {
        Self {
            intv: AbsInt::bot(),
            uintv: AbsUint::alpha(n),
            boolv: AbsBool::bot(),
            listv: AbsList::bot(),
            ptrv: AbsPtr::bot(),
            adtv: AbsAdt::bot(),
            optionv: AbsOption::bot(),
            fnv: AbsFn::bot(),
        }
    }

    pub fn list(l: Vec<AbsValue>) -> Self {
        Self {
            intv: AbsInt::bot(),
            uintv: AbsUint::bot(),
            boolv: AbsBool::bot(),
            listv: AbsList::List(l),
            ptrv: AbsPtr::bot(),
            adtv: AbsAdt::bot(),
            optionv: AbsOption::bot(),
            fnv: AbsFn::bot(),
        }
    }

    pub fn not(&self) -> Self {
        Self {
            intv: self.intv.not(),
            uintv: self.uintv.not(),
            boolv: self.boolv.not(),
            listv: AbsList::bot(),
            ptrv: AbsPtr::bot(),
            adtv: AbsAdt::bot(),
            optionv: AbsOption::bot(),
            fnv: AbsFn::bot(),
        }
    }

    pub fn neg(&self) -> Self {
        Self {
            intv: self.intv.neg(),
            uintv: AbsUint::bot(),
            boolv: AbsBool::bot(),
            listv: AbsList::bot(),
            ptrv: AbsPtr::bot(),
            adtv: AbsAdt::bot(),
            optionv: AbsOption::bot(),
            fnv: AbsFn::bot(),
        }
    }

    pub fn add(&self, other: &Self) -> Self {
        Self {
            intv: self.intv.add(&other.intv),
            uintv: self.uintv.add(&other.uintv),
            boolv: AbsBool::bot(),
            listv: AbsList::bot(),
            ptrv: AbsPtr::bot(),
            adtv: AbsAdt::bot(),
            optionv: AbsOption::bot(),
            fnv: AbsFn::bot(),
        }
    }

    pub fn sub(&self, other: &Self) -> Self {
        Self {
            intv: self.intv.sub(&other.intv),
            uintv: self.uintv.sub(&other.uintv),
            boolv: AbsBool::bot(),
            listv: AbsList::bot(),
            ptrv: AbsPtr::bot(),
            adtv: AbsAdt::bot(),
            optionv: AbsOption::bot(),
            fnv: AbsFn::bot(),
        }
    }

    pub fn mul(&self, other: &Self) -> Self {
        Self {
            intv: self.intv.mul(&other.intv),
            uintv: self.uintv.mul(&other.uintv),
            boolv: AbsBool::bot(),
            listv: AbsList::bot(),
            ptrv: AbsPtr::bot(),
            adtv: AbsAdt::bot(),
            optionv: AbsOption::bot(),
            fnv: AbsFn::bot(),
        }
    }

    pub fn div(&self, other: &Self) -> Self {
        Self {
            intv: self.intv.div(&other.intv),
            uintv: self.uintv.div(&other.uintv),
            boolv: AbsBool::bot(),
            listv: AbsList::bot(),
            ptrv: AbsPtr::bot(),
            adtv: AbsAdt::bot(),
            optionv: AbsOption::bot(),
            fnv: AbsFn::bot(),
        }
    }

    pub fn rem(&self, other: &Self) -> Self {
        Self {
            intv: self.intv.rem(&other.intv),
            uintv: self.uintv.rem(&other.uintv),
            boolv: AbsBool::bot(),
            listv: AbsList::bot(),
            ptrv: AbsPtr::bot(),
            adtv: AbsAdt::bot(),
            optionv: AbsOption::bot(),
            fnv: AbsFn::bot(),
        }
    }

    pub fn bit_xor(&self, other: &Self) -> Self {
        Self {
            intv: self.intv.bit_xor(&other.intv),
            uintv: self.uintv.bit_xor(&other.uintv),
            boolv: AbsBool::bot(),
            listv: AbsList::bot(),
            ptrv: AbsPtr::bot(),
            adtv: AbsAdt::bot(),
            optionv: AbsOption::bot(),
            fnv: AbsFn::bot(),
        }
    }

    pub fn bit_and(&self, other: &Self) -> Self {
        Self {
            intv: self.intv.bit_and(&other.intv),
            uintv: self.uintv.bit_and(&other.uintv),
            boolv: AbsBool::bot(),
            listv: AbsList::bot(),
            ptrv: AbsPtr::bot(),
            adtv: AbsAdt::bot(),
            optionv: AbsOption::bot(),
            fnv: AbsFn::bot(),
        }
    }

    pub fn bit_or(&self, other: &Self) -> Self {
        Self {
            intv: self.intv.bit_or(&other.intv),
            uintv: self.uintv.bit_or(&other.uintv),
            boolv: AbsBool::bot(),
            listv: AbsList::bot(),
            ptrv: AbsPtr::bot(),
            adtv: AbsAdt::bot(),
            optionv: AbsOption::bot(),
            fnv: AbsFn::bot(),
        }
    }

    pub fn shl(&self, other: &Self) -> Self {
        Self {
            intv: self.intv.shl(&other.intv),
            uintv: self.uintv.shl(&other.uintv),
            boolv: AbsBool::bot(),
            listv: AbsList::bot(),
            ptrv: AbsPtr::bot(),
            adtv: AbsAdt::bot(),
            optionv: AbsOption::bot(),
            fnv: AbsFn::bot(),
        }
    }

    pub fn shr(&self, other: &Self) -> Self {
        Self {
            intv: self.intv.shr(&other.intv),
            uintv: self.uintv.shr(&other.uintv),
            boolv: AbsBool::bot(),
            listv: AbsList::bot(),
            ptrv: AbsPtr::bot(),
            adtv: AbsAdt::bot(),
            optionv: AbsOption::bot(),
            fnv: AbsFn::bot(),
        }
    }

    pub fn eq(&self, other: &Self) -> Self {
        Self {
            intv: AbsInt::bot(),
            uintv: AbsUint::bot(),
            boolv: self
                .intv
                .eq(&other.intv)
                .join(&self.uintv.eq(&other.uintv))
                .join(&self.boolv.eq(&other.boolv)),
            listv: AbsList::bot(),
            ptrv: AbsPtr::bot(),
            adtv: AbsAdt::bot(),
            optionv: AbsOption::bot(),
            fnv: AbsFn::bot(),
        }
    }

    pub fn lt(&self, other: &Self) -> Self {
        Self {
            intv: AbsInt::bot(),
            uintv: AbsUint::bot(),
            boolv: self.intv.lt(&other.intv).join(&self.uintv.lt(&other.uintv)),
            listv: AbsList::bot(),
            ptrv: AbsPtr::bot(),
            adtv: AbsAdt::bot(),
            optionv: AbsOption::bot(),
            fnv: AbsFn::bot(),
        }
    }

    pub fn le(&self, other: &Self) -> Self {
        Self {
            intv: AbsInt::bot(),
            uintv: AbsUint::bot(),
            boolv: self.intv.le(&other.intv).join(&self.uintv.le(&other.uintv)),
            listv: AbsList::bot(),
            ptrv: AbsPtr::bot(),
            adtv: AbsAdt::bot(),
            optionv: AbsOption::bot(),
            fnv: AbsFn::bot(),
        }
    }

    pub fn ne(&self, other: &Self) -> Self {
        Self {
            intv: AbsInt::bot(),
            uintv: AbsUint::bot(),
            boolv: self
                .intv
                .ne(&other.intv)
                .join(&self.uintv.ne(&other.uintv))
                .join(&self.boolv.ne(&other.boolv)),
            listv: AbsList::bot(),
            ptrv: AbsPtr::bot(),
            adtv: AbsAdt::bot(),
            optionv: AbsOption::bot(),
            fnv: AbsFn::bot(),
        }
    }

    pub fn ge(&self, other: &Self) -> Self {
        Self {
            intv: AbsInt::bot(),
            uintv: AbsUint::bot(),
            boolv: self.intv.ge(&other.intv).join(&self.uintv.ge(&other.uintv)),
            listv: AbsList::bot(),
            ptrv: AbsPtr::bot(),
            adtv: AbsAdt::bot(),
            optionv: AbsOption::bot(),
            fnv: AbsFn::bot(),
        }
    }

    pub fn gt(&self, other: &Self) -> Self {
        Self {
            intv: AbsInt::bot(),
            uintv: AbsUint::bot(),
            boolv: self.intv.gt(&other.intv).join(&self.uintv.gt(&other.uintv)),
            listv: AbsList::bot(),
            ptrv: AbsPtr::bot(),
            adtv: AbsAdt::bot(),
            optionv: AbsOption::bot(),
            fnv: AbsFn::bot(),
        }
    }
}

const MAX_SIZE: usize = 10;

#[derive(Debug, Clone)]
pub enum AbsInt {
    Top,
    Set(BTreeSet<i128>),
}

impl AbsInt {
    pub fn top() -> Self {
        Self::Top
    }

    pub fn bot() -> Self {
        Self::alphas(BTreeSet::new())
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

#[derive(Debug, Clone)]
pub enum AbsUint {
    Top,
    Set(BTreeSet<u128>),
}

impl AbsUint {
    pub fn top() -> Self {
        Self::Top
    }

    pub fn bot() -> Self {
        Self::alphas(BTreeSet::new())
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

#[derive(Debug, Clone, Copy)]
pub enum AbsBool {
    Top,
    True,
    False,
    Bot,
}

impl AbsBool {
    pub fn top() -> Self {
        Self::Top
    }

    pub fn bot() -> Self {
        Self::Bot
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
