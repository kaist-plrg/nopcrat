use std::collections::{BTreeMap, BTreeSet};

use etrace::some_or;
use rustc_span::def_id::DefId;

#[derive(Debug, Clone)]
pub struct AbsState {
    pub local: AbsLocal,
    pub heap: AbsHeap,
    pub writes: MustPathSet,
    pub reads: MayPathSet,
}

impl AbsState {
    pub fn bot(len: usize) -> Self {
        Self {
            local: AbsLocal::bot(len),
            heap: AbsHeap::bot(),
            writes: MustPathSet::bot(),
            reads: MayPathSet::bot(),
        }
    }

    pub fn join(&self, other: &Self) -> Self {
        Self {
            local: self.local.join(&other.local),
            heap: self.heap.join(&other.heap),
            writes: self.writes.join(&other.writes),
            reads: self.reads.join(&other.reads),
        }
    }

    pub fn ord(&self, other: &Self) -> bool {
        self.local.ord(&other.local)
            && self.heap.ord(&other.heap)
            && self.writes.ord(&other.writes)
            && self.reads.ord(&other.reads)
    }

    pub fn get(&self, base: AbsBase) -> Option<&AbsValue> {
        match base {
            AbsBase::Local(i) => self.local.0.get(i),
            AbsBase::Heap(i) => self.heap.0.get(i),
            AbsBase::Null => None,
        }
    }

    pub fn get_mut(&mut self, base: AbsBase) -> Option<&mut AbsValue> {
        match base {
            AbsBase::Local(i) => self.local.0.get_mut(i),
            AbsBase::Heap(i) => self.heap.0.get_mut(i),
            AbsBase::Null => None,
        }
    }

    pub fn add_reads<I: Iterator<Item = AbsPath>>(&mut self, paths: I) {
        for path in paths {
            if !self.writes.contains(&path) {
                self.reads.insert(path);
            }
        }
    }

    pub fn add_writes<I: Iterator<Item = AbsPath>>(&mut self, paths: I) {
        for path in paths {
            if !self.reads.contains(&path) {
                self.writes.insert(path);
            }
        }
    }
}

#[derive(Clone)]
pub struct AbsHeap(Vec<AbsValue>);

impl std::fmt::Debug for AbsHeap {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

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

    pub fn push(&mut self, v: AbsValue) -> usize {
        self.0.push(v);
        self.0.len() - 1
    }

    pub fn get(&self, i: usize) -> &AbsValue {
        &self.0[i]
    }
}

#[derive(Clone)]
pub struct AbsLocal(Vec<AbsValue>);

impl std::fmt::Debug for AbsLocal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

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

    pub fn get_mut(&mut self, i: usize) -> &mut AbsValue {
        &mut self.0[i]
    }

    pub fn set(&mut self, i: usize, v: AbsValue) {
        self.0[i] = v;
    }

    pub fn iter(&self) -> impl Iterator<Item = &AbsValue> {
        self.0.iter()
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
            && self.optionv.ord(&other.optionv)
            && self.fnv.ord(&other.fnv)
    }

    pub fn is_bot(&self) -> bool {
        self.intv.is_bot()
            && self.uintv.is_bot()
            && self.floatv.is_bot()
            && self.boolv.is_bot()
            && self.listv.is_bot()
            && self.ptrv.is_bot()
            && self.optionv.is_bot()
            && self.fnv.is_bot()
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

    pub fn bools(boolv: AbsBool) -> Self {
        Self {
            boolv,
            ..Self::bot()
        }
    }

    pub fn list(l: Vec<AbsValue>) -> Self {
        Self {
            listv: AbsList::List(l),
            ..Self::bot()
        }
    }

    pub fn ptr(ptrv: AbsPtr) -> Self {
        Self {
            ptrv,
            ..Self::bot()
        }
    }

    pub fn option(optionv: AbsOption) -> Self {
        Self {
            optionv,
            ..Self::bot()
        }
    }

    pub fn func(fnv: AbsFn) -> Self {
        Self { fnv, ..Self::bot() }
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

    pub fn heap_addr(&self) -> usize {
        self.ptrv.heap_addr()
    }

    pub fn compare_pointers<'a, 'b>(&'a self, other: &'b Self) -> Vec<(&'a AbsPtr, &'b AbsPtr)> {
        let mut res = vec![];
        if !self.ptrv.is_bot() && !other.ptrv.is_bot() {
            res.push((&self.ptrv, &other.ptrv));
        }
        if let (AbsList::List(l1), AbsList::List(l2)) = (&self.listv, &other.listv) {
            for (v1, v2) in l1.iter().zip(l2.iter()) {
                res.extend(v1.compare_pointers(v2));
            }
        }
        res
    }

    pub fn subst(&self, map: &BTreeMap<usize, AbsPtr>) -> Self {
        Self {
            ptrv: self.ptrv.subst(map),
            listv: self.listv.subst(map),
            ..self.clone()
        }
    }

    pub fn allocs(&self) -> BTreeSet<usize> {
        self.ptrv
            .allocs()
            .union(&self.listv.allocs())
            .cloned()
            .collect()
    }
}

const MAX_SIZE: usize = 11;

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

    pub fn is_top(&self) -> bool {
        matches!(self, Self::Top)
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

    pub fn gamma(&self) -> Option<&BTreeSet<i128>> {
        if let Self::Set(s) = self {
            Some(s)
        } else {
            None
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

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
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

    pub fn gamma(&self) -> Option<&BTreeSet<u128>> {
        if let Self::Set(s) = self {
            Some(s)
        } else {
            None
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

    pub fn gamma(&self) -> Option<Vec<f64>> {
        if let Self::Set(s) = self {
            Some(s.iter().map(|n| f64::from_bits(*n)).collect())
        } else {
            None
        }
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
            Self::Top => write!(f, "Top_b"),
            Self::True => write!(f, "true"),
            Self::False => write!(f, "false"),
            Self::Bot => write!(f, "Bot_b"),
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

    pub fn gamma(&self) -> Vec<bool> {
        match self {
            Self::Top => vec![true, false],
            Self::True => vec![true],
            Self::False => vec![false],
            Self::Bot => vec![],
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
            (Self::False, _) | (_, Self::False) => Self::False,
            (Self::True, Self::True) => Self::True,
            _ => Self::Top,
        }
    }

    pub fn bit_or(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Bot, _) | (_, Self::Bot) => Self::Bot,
            (Self::True, _) | (_, Self::True) => Self::True,
            (Self::False, Self::False) => Self::False,
            _ => Self::Top,
        }
    }
}

#[derive(Clone)]
pub enum AbsList {
    Top,
    List(Vec<AbsValue>),
    Bot,
}

impl std::fmt::Debug for AbsList {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Top => write!(f, "Top_l"),
            Self::List(l) => {
                write!(f, "[")?;
                for (i, v) in l.iter().enumerate() {
                    if i != 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{:?}", v)?;
                }
                write!(f, "]")
            }
            Self::Bot => write!(f, "Bot_l"),
        }
    }
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

    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> Option<usize> {
        if let Self::List(l) = self {
            Some(l.len())
        } else {
            None
        }
    }

    pub fn get_mut(&mut self, i: usize) -> Option<&mut AbsValue> {
        if let Self::List(l) = self {
            l.get_mut(i)
        } else {
            None
        }
    }

    pub fn subst(&self, map: &BTreeMap<usize, AbsPtr>) -> Self {
        match self {
            Self::Top => Self::Top,
            Self::List(l) => Self::List(l.iter().map(|v| v.subst(map)).collect()),
            Self::Bot => Self::Bot,
        }
    }

    pub fn allocs(&self) -> BTreeSet<usize> {
        if let Self::List(l) = self {
            l.iter().flat_map(|v| v.allocs()).collect()
        } else {
            BTreeSet::new()
        }
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct AbsPlace {
    pub base: AbsBase,
    pub projection: Vec<AbsProjElem>,
}

impl std::fmt::Debug for AbsPlace {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.base)?;
        for elem in &self.projection {
            write!(f, "{:?}", elem)?;
        }
        Ok(())
    }
}

impl AbsPlace {
    pub fn null() -> Self {
        Self {
            base: AbsBase::Null,
            projection: Vec::new(),
        }
    }

    pub fn alloc(i: usize) -> Self {
        Self {
            base: AbsBase::Heap(i),
            projection: Vec::new(),
        }
    }

    pub fn is_null(&self) -> bool {
        self.base == AbsBase::Null
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum AbsBase {
    Local(usize),
    Heap(usize),
    Null,
}

impl std::fmt::Debug for AbsBase {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Local(i) => write!(f, "_{}", i),
            Self::Heap(i) => write!(f, "A{}", i),
            Self::Null => write!(f, "null"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum AbsProjElem {
    Field(usize),
    Index(AbsUint),
}

impl std::fmt::Debug for AbsProjElem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Field(i) => write!(f, ".{}", i),
            Self::Index(i) => write!(f, "[{:?}]", i),
        }
    }
}

#[derive(Clone)]
pub enum AbsPtr {
    Top,
    Set(BTreeSet<AbsPlace>),
}

impl std::fmt::Debug for AbsPtr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Top => write!(f, "Top_p"),
            Self::Set(s) => match s.len() {
                0 => write!(f, "Bot_p"),
                1 => write!(f, "{:?}", s.first().unwrap()),
                _ => {
                    write!(f, "{{")?;
                    for (i, ptr) in s.iter().enumerate() {
                        if i != 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{:?}", ptr)?;
                    }
                    write!(f, "}}")
                }
            },
        }
    }
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

    pub fn alpha(n: AbsPlace) -> Self {
        Self::alphas([n].into_iter().collect())
    }

    pub fn alphas(set: BTreeSet<AbsPlace>) -> Self {
        if set.len() > MAX_SIZE {
            Self::Top
        } else {
            Self::Set(set)
        }
    }

    pub fn gamma(&self) -> Option<&BTreeSet<AbsPlace>> {
        if let Self::Set(s) = self {
            Some(s)
        } else {
            None
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

    pub fn null() -> Self {
        Self::alpha(AbsPlace::null())
    }

    pub fn heap_addr(&self) -> usize {
        let places = self.gamma().unwrap();
        assert_eq!(places.len(), 1);
        let place = places.first().unwrap();
        if let AbsBase::Heap(alloc) = place.base {
            alloc
        } else {
            panic!()
        }
    }

    pub fn subst(&self, map: &BTreeMap<usize, Self>) -> Self {
        if let Self::Set(ptrs) = self {
            ptrs.iter()
                .map(|place| {
                    let alloc = match &place.base {
                        AbsBase::Local(_) => return Self::bot(),
                        AbsBase::Heap(alloc) => alloc,
                        AbsBase::Null => return self.clone(),
                    };
                    let ptrs = if let AbsPtr::Set(ptrs) = map.get(alloc).unwrap() {
                        ptrs
                    } else {
                        return AbsPtr::Top;
                    };
                    Self::Set(
                        ptrs.iter()
                            .cloned()
                            .map(|mut new_place| {
                                new_place.projection.extend(place.projection.clone());
                                new_place
                            })
                            .collect(),
                    )
                })
                .reduce(|ptr1, ptr2| ptr1.join(&ptr2))
                .unwrap_or(AbsPtr::bot())
        } else {
            AbsPtr::Top
        }
    }

    pub fn allocs(&self) -> BTreeSet<usize> {
        if let Self::Set(ptrs) = self {
            ptrs.iter()
                .filter_map(|place| match &place.base {
                    AbsBase::Local(_) => None,
                    AbsBase::Heap(alloc) => Some(*alloc),
                    AbsBase::Null => None,
                })
                .collect()
        } else {
            BTreeSet::new()
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

    pub fn is_none(&self) -> bool {
        matches!(self, Self::None)
    }

    pub fn some(v: AbsValue) -> Self {
        Self::Some(Box::new(v))
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

    pub fn gamma(&self) -> Option<&BTreeSet<DefId>> {
        if let Self::Set(s) = self {
            Some(s)
        } else {
            None
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

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct AbsPath(pub Vec<usize>);

impl std::fmt::Debug for AbsPath {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut first = true;
        for idx in self.0.iter() {
            if first {
                first = false;
            } else {
                write!(f, ".")?;
            }
            write!(f, "{}", idx)?;
        }
        Ok(())
    }
}

impl AbsPath {
    pub fn base(&self) -> usize {
        self.0[0]
    }

    pub fn from_place(
        place: &AbsPlace,
        alloc_param_map: &BTreeMap<usize, usize>,
    ) -> Option<(Self, bool)> {
        let alloc = if let AbsBase::Heap(alloc) = place.base {
            alloc
        } else {
            return None;
        };
        let param = some_or!(alloc_param_map.get(&alloc), return None);
        let mut projections = vec![*param];
        let mut array_access = false;
        for proj in place.projection.iter() {
            match proj {
                AbsProjElem::Field(idx) => projections.push(*idx),
                AbsProjElem::Index(_) => {
                    array_access = true;
                    break;
                }
            }
        }
        Some((Self(projections), array_access))
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum MustPathSet {
    All,
    Set(BTreeSet<AbsPath>),
}

impl std::fmt::Debug for MustPathSet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MustPathSet::All => write!(f, "All"),
            MustPathSet::Set(s) => write!(f, "{:?}", s),
        }
    }
}

impl MustPathSet {
    pub fn top() -> Self {
        Self::Set(BTreeSet::new())
    }

    pub fn bot() -> Self {
        Self::All
    }

    pub fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (s, Self::All) | (Self::All, s) => s.clone(),
            (Self::Set(s1), Self::Set(s2)) => Self::Set(s1.intersection(s2).cloned().collect()),
        }
    }

    pub fn ord(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::All, _) => true,
            (_, Self::All) => false,
            (Self::Set(s1), Self::Set(s2)) => s2.is_subset(s1),
        }
    }

    pub fn insert(&mut self, place: AbsPath) {
        if let Self::Set(set) = self {
            set.insert(place);
        }
    }

    pub fn contains(&self, place: &AbsPath) -> bool {
        match self {
            Self::All => true,
            Self::Set(set) => set.contains(place),
        }
    }

    pub fn is_empty(&self) -> bool {
        match self {
            Self::All => false,
            Self::Set(set) => set.is_empty(),
        }
    }

    pub fn len(&self) -> usize {
        match self {
            Self::All => panic!(),
            Self::Set(set) => set.len(),
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = &AbsPath> {
        match self {
            Self::All => panic!(),
            Self::Set(set) => set.iter(),
        }
    }

    pub fn as_set(&self) -> &BTreeSet<AbsPath> {
        match self {
            Self::All => panic!(),
            Self::Set(set) => set,
        }
    }

    pub fn as_vec(&self) -> Vec<&AbsPath> {
        match self {
            Self::All => panic!(),
            Self::Set(set) => set.iter().collect(),
        }
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct MayPathSet(BTreeSet<AbsPath>);

impl std::fmt::Debug for MayPathSet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

impl MayPathSet {
    pub fn bot() -> Self {
        Self(BTreeSet::new())
    }

    pub fn join(&self, other: &Self) -> Self {
        Self(self.0.union(&other.0).cloned().collect())
    }

    pub fn ord(&self, other: &Self) -> bool {
        self.0.is_subset(&other.0)
    }

    pub fn insert(&mut self, place: AbsPath) {
        self.0.insert(place);
    }

    pub fn contains(&self, place: &AbsPath) -> bool {
        self.0.contains(place)
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn iter(&self) -> impl Iterator<Item = &AbsPath> {
        self.0.iter()
    }

    pub fn as_set(&self) -> &BTreeSet<AbsPath> {
        &self.0
    }

    pub fn as_vec(&self) -> Vec<&AbsPath> {
        self.0.iter().collect()
    }
}
