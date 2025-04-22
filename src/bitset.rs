// from rustc_index/src/bit_set.rs (nightly-2023-09-05)

use std::{
    fmt, iter,
    marker::PhantomData,
    ops::{Bound, RangeBounds},
    slice,
};

use arrayvec::ArrayVec;
use rustc_index::{
    bit_set::{BitRelations, DenseBitSet},
    Idx,
};
use smallvec::{smallvec, SmallVec};

type Word = u64;
const WORD_BYTES: usize = size_of::<Word>();
const WORD_BITS: usize = WORD_BYTES * 8;

#[inline]
fn inclusive_start_end<T: Idx>(
    range: impl RangeBounds<T>,
    domain: usize,
) -> Option<(usize, usize)> {
    // Both start and end are inclusive.
    let start = match range.start_bound().cloned() {
        Bound::Included(start) => start.index(),
        Bound::Excluded(start) => start.index() + 1,
        Bound::Unbounded => 0,
    };
    let end = match range.end_bound().cloned() {
        Bound::Included(end) => end.index(),
        Bound::Excluded(end) => end.index().checked_sub(1)?,
        Bound::Unbounded => domain - 1,
    };
    assert!(end < domain);
    if start > end {
        return None;
    }
    Some((start, end))
}

macro_rules! bit_relations_inherent_impls {
    () => {
        /// Sets `self = self | other` and returns `true` if `self` changed
        /// (i.e., if new bits were added).
        pub fn union<Rhs>(&mut self, other: &Rhs) -> bool
        where Self: BitRelations<Rhs> {
            <Self as BitRelations<Rhs>>::union(self, other)
        }

        /// Sets `self = self - other` and returns `true` if `self` changed.
        /// (i.e., if any bits were removed).
        pub fn subtract<Rhs>(&mut self, other: &Rhs) -> bool
        where Self: BitRelations<Rhs> {
            <Self as BitRelations<Rhs>>::subtract(self, other)
        }

        /// Sets `self = self & other` and return `true` if `self` changed.
        /// (i.e., if any bits were removed).
        pub fn intersect<Rhs>(&mut self, other: &Rhs) -> bool
        where Self: BitRelations<Rhs> {
            <Self as BitRelations<Rhs>>::intersect(self, other)
        }
    };
}

/// A fixed-size bitset type with a dense representation.
///
/// NOTE: Use [`GrowableBitSet`] if you need support for resizing after creation.
///
/// `T` is an index type, typically a newtyped `usize` wrapper, but it can also
/// just be `usize`.
///
/// All operations that involve an element will panic if the element is equal
/// to or greater than the domain size. All operations that involve two bitsets
/// will panic if the bitsets have differing domain sizes.
#[derive(Eq, PartialEq, Hash)]
pub struct BitSet<T> {
    domain_size: usize,
    words: SmallVec<[Word; 2]>,
    marker: PhantomData<T>,
}

impl<T> BitSet<T> {
    /// Gets the domain size.
    pub fn domain_size(&self) -> usize {
        self.domain_size
    }
}

impl<T: Idx> BitSet<T> {
    bit_relations_inherent_impls! {}

    /// Creates a new, empty bitset with a given `domain_size`.
    #[inline]
    pub fn new_empty(domain_size: usize) -> BitSet<T> {
        let num_words = num_words(domain_size);
        BitSet {
            domain_size,
            words: smallvec![0; num_words],
            marker: PhantomData,
        }
    }

    /// Creates a new, filled bitset with a given `domain_size`.
    #[inline]
    pub fn new_filled(domain_size: usize) -> BitSet<T> {
        let num_words = num_words(domain_size);
        let mut result = BitSet {
            domain_size,
            words: smallvec![!0; num_words],
            marker: PhantomData,
        };
        result.clear_excess_bits();
        result
    }

    /// Clear all elements.
    #[inline]
    pub fn clear(&mut self) {
        self.words.fill(0);
    }

    /// Creates a new bitset with the same elements as the rustc's `DenseBitSet`.
    #[inline]
    pub fn from_dense(dense: &DenseBitSet<T>) -> Self {
        // println!("from dense {:?}", dense);
        let mut result = BitSet::new_empty(dense.domain_size());
        for elem in dense.iter() {
            result.insert(elem);
        }
        // println!("to bitset  {:?}", result);
        result
    }

    /// Clear excess bits in the final word.
    fn clear_excess_bits(&mut self) {
        clear_excess_bits_in_final_word(self.domain_size, &mut self.words);
    }

    /// Count the number of set bits in the set.
    pub fn count(&self) -> usize {
        self.words.iter().map(|e| e.count_ones() as usize).sum()
    }

    /// Returns `true` if `self` contains `elem`.
    #[inline]
    pub fn contains(&self, elem: T) -> bool {
        assert!(elem.index() < self.domain_size);
        let (word_index, mask) = word_index_and_mask(elem);
        (self.words[word_index] & mask) != 0
    }

    /// Is `self` is a (non-strict) superset of `other`?
    #[inline]
    pub fn superset(&self, other: &BitSet<T>) -> bool {
        assert_eq!(self.domain_size, other.domain_size);
        self.words
            .iter()
            .zip(&other.words)
            .all(|(a, b)| (a & b) == *b)
    }

    /// Is the set empty?
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.words.iter().all(|a| *a == 0)
    }

    /// Insert `elem`. Returns whether the set has changed.
    #[inline]
    pub fn insert(&mut self, elem: T) -> bool {
        assert!(elem.index() < self.domain_size);
        let (word_index, mask) = word_index_and_mask(elem);
        let word_ref = &mut self.words[word_index];
        let word = *word_ref;
        let new_word = word | mask;
        *word_ref = new_word;
        new_word != word
    }

    #[inline]
    pub fn insert_range(&mut self, elems: impl RangeBounds<T>) {
        let Some((start, end)) = inclusive_start_end(elems, self.domain_size) else {
            return;
        };

        let (start_word_index, start_mask) = word_index_and_mask(start);
        let (end_word_index, end_mask) = word_index_and_mask(end);

        // Set all words in between start and end (exclusively of both).
        for word_index in (start_word_index + 1)..end_word_index {
            self.words[word_index] = !0;
        }

        if start_word_index != end_word_index {
            // Start and end are in different words, so we handle each in turn.
            //
            // We set all leading bits. This includes the start_mask bit.
            self.words[start_word_index] |= !(start_mask - 1);
            // And all trailing bits (i.e. from 0..=end) in the end word,
            // including the end.
            self.words[end_word_index] |= end_mask | (end_mask - 1);
        } else {
            self.words[start_word_index] |= end_mask | (end_mask - start_mask);
        }
    }

    /// Sets all bits to true.
    pub fn insert_all(&mut self) {
        self.words.fill(!0);
        self.clear_excess_bits();
    }

    /// Returns `true` if the set has changed.
    #[inline]
    pub fn remove(&mut self, elem: T) -> bool {
        assert!(elem.index() < self.domain_size);
        let (word_index, mask) = word_index_and_mask(elem);
        let word_ref = &mut self.words[word_index];
        let word = *word_ref;
        let new_word = word & !mask;
        *word_ref = new_word;
        new_word != word
    }

    /// Gets a slice of the underlying words.
    pub fn words(&self) -> &[Word] {
        &self.words
    }

    /// Iterates over the indices of set bits in a sorted order.
    #[inline]
    pub fn iter(&self) -> BitIter<'_, T> {
        BitIter::new(&self.words)
    }

    /// Duplicates the set as a hybrid set.
    pub fn to_hybrid(&self) -> HybridBitSet<T> {
        // Note: we currently don't bother trying to make a Sparse set.
        HybridBitSet::Dense(self.to_owned())
    }

    /// Set `self = self | other`. In contrast to `union` returns `true` if the set contains at
    /// least one bit that is not in `other` (i.e. `other` is not a superset of `self`).
    ///
    /// This is an optimization for union of a hybrid bitset.
    fn reverse_union_sparse(&mut self, sparse: &SparseBitSet<T>) -> bool {
        assert!(sparse.domain_size == self.domain_size);
        self.clear_excess_bits();

        let mut not_already = false;
        // Index of the current word not yet merged.
        let mut current_index = 0;
        // Mask of bits that came from the sparse set in the current word.
        let mut new_bit_mask = 0;
        for (word_index, mask) in sparse.iter().map(|x| word_index_and_mask(*x)) {
            // Next bit is in a word not inspected yet.
            if word_index > current_index {
                self.words[current_index] |= new_bit_mask;
                // Were there any bits in the old word that did not occur in the sparse set?
                not_already |= (self.words[current_index] ^ new_bit_mask) != 0;
                // Check all words we skipped for any set bit.
                not_already |= self.words[current_index + 1..word_index]
                    .iter()
                    .any(|&x| x != 0);
                // Update next word.
                current_index = word_index;
                // Reset bit mask, no bits have been merged yet.
                new_bit_mask = 0;
            }
            // Add bit and mark it as coming from the sparse set.
            // self.words[word_index] |= mask;
            new_bit_mask |= mask;
        }
        self.words[current_index] |= new_bit_mask;
        // Any bits in the last inspected word that were not in the sparse set?
        not_already |= (self.words[current_index] ^ new_bit_mask) != 0;
        // Any bits in the tail? Note `clear_excess_bits` before.
        not_already |= self.words[current_index + 1..].iter().any(|&x| x != 0);

        not_already
    }

    fn last_set_in(&self, range: impl RangeBounds<T>) -> Option<T> {
        let (start, end) = inclusive_start_end(range, self.domain_size)?;
        let (start_word_index, _) = word_index_and_mask(start);
        let (end_word_index, end_mask) = word_index_and_mask(end);

        let end_word = self.words[end_word_index] & (end_mask | (end_mask - 1));
        if end_word != 0 {
            let pos = max_bit(end_word) + WORD_BITS * end_word_index;
            if start <= pos {
                return Some(T::new(pos));
            }
        }

        // We exclude end_word_index from the range here, because we don't want
        // to limit ourselves to *just* the last word: the bits set it in may be
        // after `end`, so it may not work out.
        if let Some(offset) = self.words[start_word_index..end_word_index]
            .iter()
            .rposition(|&w| w != 0)
        {
            let word_idx = start_word_index + offset;
            let start_word = self.words[word_idx];
            let pos = max_bit(start_word) + WORD_BITS * word_idx;
            if start <= pos {
                return Some(T::new(pos));
            }
        }

        None
    }
}

// dense REL dense
impl<T: Idx> BitRelations<BitSet<T>> for BitSet<T> {
    fn union(&mut self, other: &BitSet<T>) -> bool {
        assert_eq!(self.domain_size, other.domain_size);
        bitwise(&mut self.words, &other.words, |a, b| a | b)
    }

    fn subtract(&mut self, other: &BitSet<T>) -> bool {
        assert_eq!(self.domain_size, other.domain_size);
        bitwise(&mut self.words, &other.words, |a, b| a & !b)
    }

    fn intersect(&mut self, other: &BitSet<T>) -> bool {
        assert_eq!(self.domain_size, other.domain_size);
        bitwise(&mut self.words, &other.words, |a, b| a & b)
    }
}

// Applies a function to mutate a bitset, and returns true if any
// of the applications return true
fn sequential_update<T: Idx>(
    mut self_update: impl FnMut(T) -> bool,
    it: impl Iterator<Item = T>,
) -> bool {
    it.fold(false, |changed, elem| self_update(elem) | changed)
}

// Optimization of intersection for SparseBitSet that's generic
// over the RHS
fn sparse_intersect<T: Idx>(
    set: &mut SparseBitSet<T>,
    other_contains: impl Fn(&T) -> bool,
) -> bool {
    let size = set.elems.len();
    set.elems.retain(|elem| other_contains(elem));
    set.elems.len() != size
}

// Optimization of dense/sparse intersection. The resulting set is
// guaranteed to be at most the size of the sparse set, and hence can be
// represented as a sparse set. Therefore the sparse set is copied and filtered,
// then returned as the new set.
fn dense_sparse_intersect<T: Idx>(
    dense: &BitSet<T>,
    sparse: &SparseBitSet<T>,
) -> (SparseBitSet<T>, bool) {
    let mut sparse_copy = sparse.clone();
    sparse_intersect(&mut sparse_copy, |el| dense.contains(*el));
    let n = sparse_copy.len();
    (sparse_copy, n != dense.count())
}

// hybrid REL dense
impl<T: Idx> BitRelations<BitSet<T>> for HybridBitSet<T> {
    fn union(&mut self, other: &BitSet<T>) -> bool {
        assert_eq!(self.domain_size(), other.domain_size);
        match self {
            HybridBitSet::Sparse(sparse) => {
                // `self` is sparse and `other` is dense. To
                // merge them, we have two available strategies:
                // * Densify `self` then merge other
                // * Clone other then integrate bits from `self`
                // The second strategy requires dedicated method
                // since the usual `union` returns the wrong
                // result. In the dedicated case the computation
                // is slightly faster if the bits of the sparse
                // bitset map to only few words of the dense
                // representation, i.e. indices are near each
                // other.
                //
                // Benchmarking seems to suggest that the second
                // option is worth it.
                let mut new_dense = other.clone();
                let changed = new_dense.reverse_union_sparse(sparse);
                *self = HybridBitSet::Dense(new_dense);
                changed
            }

            HybridBitSet::Dense(dense) => dense.union(other),
        }
    }

    fn subtract(&mut self, other: &BitSet<T>) -> bool {
        assert_eq!(self.domain_size(), other.domain_size);
        match self {
            HybridBitSet::Sparse(sparse) => {
                sequential_update(|elem| sparse.remove(elem), other.iter())
            }
            HybridBitSet::Dense(dense) => dense.subtract(other),
        }
    }

    fn intersect(&mut self, other: &BitSet<T>) -> bool {
        assert_eq!(self.domain_size(), other.domain_size);
        match self {
            HybridBitSet::Sparse(sparse) => sparse_intersect(sparse, |elem| other.contains(*elem)),
            HybridBitSet::Dense(dense) => dense.intersect(other),
        }
    }
}

// dense REL hybrid
impl<T: Idx> BitRelations<HybridBitSet<T>> for BitSet<T> {
    fn union(&mut self, other: &HybridBitSet<T>) -> bool {
        assert_eq!(self.domain_size, other.domain_size());
        match other {
            HybridBitSet::Sparse(sparse) => {
                sequential_update(|elem| self.insert(elem), sparse.iter().cloned())
            }
            HybridBitSet::Dense(dense) => self.union(dense),
        }
    }

    fn subtract(&mut self, other: &HybridBitSet<T>) -> bool {
        assert_eq!(self.domain_size, other.domain_size());
        match other {
            HybridBitSet::Sparse(sparse) => {
                sequential_update(|elem| self.remove(elem), sparse.iter().cloned())
            }
            HybridBitSet::Dense(dense) => self.subtract(dense),
        }
    }

    fn intersect(&mut self, other: &HybridBitSet<T>) -> bool {
        assert_eq!(self.domain_size, other.domain_size());
        match other {
            HybridBitSet::Sparse(sparse) => {
                let (updated, changed) = dense_sparse_intersect(self, sparse);

                // We can't directly assign the SparseBitSet to the BitSet, and
                // doing `*self = updated.to_dense()` would cause a drop / reallocation. Instead,
                // the BitSet is cleared and `updated` is copied into `self`.
                self.clear();
                for elem in updated.iter() {
                    self.insert(*elem);
                }
                changed
            }
            HybridBitSet::Dense(dense) => self.intersect(dense),
        }
    }
}

// hybrid REL hybrid
impl<T: Idx> BitRelations<HybridBitSet<T>> for HybridBitSet<T> {
    fn union(&mut self, other: &HybridBitSet<T>) -> bool {
        assert_eq!(self.domain_size(), other.domain_size());
        match self {
            HybridBitSet::Sparse(_) => {
                match other {
                    HybridBitSet::Sparse(other_sparse) => {
                        // Both sets are sparse. Add the elements in
                        // `other_sparse` to `self` one at a time. This
                        // may or may not cause `self` to be densified.
                        let mut changed = false;
                        for elem in other_sparse.iter() {
                            changed |= self.insert(*elem);
                        }
                        changed
                    }

                    HybridBitSet::Dense(other_dense) => self.union(other_dense),
                }
            }

            HybridBitSet::Dense(self_dense) => self_dense.union(other),
        }
    }

    fn subtract(&mut self, other: &HybridBitSet<T>) -> bool {
        assert_eq!(self.domain_size(), other.domain_size());
        match self {
            HybridBitSet::Sparse(self_sparse) => {
                sequential_update(|elem| self_sparse.remove(elem), other.iter())
            }
            HybridBitSet::Dense(self_dense) => self_dense.subtract(other),
        }
    }

    fn intersect(&mut self, other: &HybridBitSet<T>) -> bool {
        assert_eq!(self.domain_size(), other.domain_size());
        match self {
            HybridBitSet::Sparse(self_sparse) => {
                sparse_intersect(self_sparse, |elem| other.contains(*elem))
            }
            HybridBitSet::Dense(self_dense) => match other {
                HybridBitSet::Sparse(other_sparse) => {
                    let (updated, changed) = dense_sparse_intersect(self_dense, other_sparse);
                    *self = HybridBitSet::Sparse(updated);
                    changed
                }
                HybridBitSet::Dense(other_dense) => self_dense.intersect(other_dense),
            },
        }
    }
}

impl<T> Clone for BitSet<T> {
    fn clone(&self) -> Self {
        BitSet {
            domain_size: self.domain_size,
            words: self.words.clone(),
            marker: PhantomData,
        }
    }

    fn clone_from(&mut self, from: &Self) {
        self.domain_size = from.domain_size;
        self.words.clone_from(&from.words);
    }
}

impl<T: Idx> fmt::Debug for BitSet<T> {
    fn fmt(&self, w: &mut fmt::Formatter<'_>) -> fmt::Result {
        w.debug_list().entries(self.iter()).finish()
    }
}

impl<T: Idx> fmt::Display for BitSet<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut sep = '[';

        // Note: this is a little endian printout of bytes.

        // i tracks how many bits we have printed so far.
        let mut i = 0;
        for word in &self.words {
            let mut word = *word;
            for _ in 0..WORD_BYTES {
                let remain = self.domain_size - i;
                // If less than a byte remains, then mask just that many bits.
                let mask = if remain <= 8 { (1 << remain) - 1 } else { 0xFF };
                debug_assert!(mask <= 0xFF);
                let byte = word & mask;

                write!(f, "{sep}{byte:02x}")?;

                if remain <= 8 {
                    break;
                }
                word >>= 8;
                i += 8;
                sep = '-';
            }
            sep = '|';
        }

        write!(f, "]")
    }
}

#[derive(Debug)]
pub struct BitIter<'a, T: Idx> {
    /// A copy of the current word, but with any already-visited bits cleared.
    /// (This lets us use `trailing_zeros()` to find the next set bit.) When it
    /// is reduced to 0, we move onto the next word.
    word: Word,

    /// The offset (measured in bits) of the current word.
    offset: usize,

    /// Underlying iterator over the words.
    iter: slice::Iter<'a, Word>,

    marker: PhantomData<T>,
}

impl<'a, T: Idx> BitIter<'a, T> {
    #[inline]
    fn new(words: &'a [Word]) -> BitIter<'a, T> {
        // We initialize `word` and `offset` to degenerate values. On the first
        // call to `next()` we will fall through to getting the first word from
        // `iter`, which sets `word` to the first word (if there is one) and
        // `offset` to 0. Doing it this way saves us from having to maintain
        // additional state about whether we have started.
        BitIter {
            word: 0,
            offset: usize::MAX - (WORD_BITS - 1),
            iter: words.iter(),
            marker: PhantomData,
        }
    }
}

impl<T: Idx> Iterator for BitIter<'_, T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        loop {
            if self.word != 0 {
                // Get the position of the next set bit in the current word,
                // then clear the bit.
                let bit_pos = self.word.trailing_zeros() as usize;
                let bit = 1 << bit_pos;
                self.word ^= bit;
                return Some(T::new(bit_pos + self.offset));
            }

            // Move onto the next word. `wrapping_add()` is needed to handle
            // the degenerate initial value given to `offset` in `new()`.
            let word = self.iter.next()?;
            self.word = *word;
            self.offset = self.offset.wrapping_add(WORD_BITS);
        }
    }
}

#[inline]
fn bitwise<Op>(out_vec: &mut [Word], in_vec: &[Word], op: Op) -> bool
where Op: Fn(Word, Word) -> Word {
    assert_eq!(out_vec.len(), in_vec.len());
    let mut changed = 0;
    for (out_elem, in_elem) in iter::zip(out_vec, in_vec) {
        let old_val = *out_elem;
        let new_val = op(old_val, *in_elem);
        *out_elem = new_val;
        // This is essentially equivalent to a != with changed being a bool, but
        // in practice this code gets auto-vectorized by the compiler for most
        // operators. Using != here causes us to generate quite poor code as the
        // compiler tries to go back to a boolean on each loop iteration.
        changed |= old_val ^ new_val;
    }
    changed != 0
}

const SPARSE_MAX: usize = 8;

/// A fixed-size bitset type with a sparse representation and a maximum of
/// `SPARSE_MAX` elements. The elements are stored as a sorted `ArrayVec` with
/// no duplicates.
///
/// This type is used by `HybridBitSet`; do not use directly.
#[derive(Clone, Debug)]
pub struct SparseBitSet<T> {
    domain_size: usize,
    elems: ArrayVec<T, SPARSE_MAX>,
}

impl<T: Idx> SparseBitSet<T> {
    bit_relations_inherent_impls! {}

    fn new_empty(domain_size: usize) -> Self {
        SparseBitSet {
            domain_size,
            elems: ArrayVec::new(),
        }
    }

    fn len(&self) -> usize {
        self.elems.len()
    }

    fn is_empty(&self) -> bool {
        self.elems.len() == 0
    }

    fn contains(&self, elem: T) -> bool {
        assert!(elem.index() < self.domain_size);
        self.elems.contains(&elem)
    }

    fn insert(&mut self, elem: T) -> bool {
        assert!(elem.index() < self.domain_size);
        let changed = if let Some(i) = self.elems.iter().position(|&e| e.index() >= elem.index()) {
            if self.elems[i] == elem {
                // `elem` is already in the set.
                false
            } else {
                // `elem` is smaller than one or more existing elements.
                self.elems.insert(i, elem);
                true
            }
        } else {
            // `elem` is larger than all existing elements.
            self.elems.push(elem);
            true
        };
        assert!(self.len() <= SPARSE_MAX);
        changed
    }

    fn remove(&mut self, elem: T) -> bool {
        assert!(elem.index() < self.domain_size);
        if let Some(i) = self.elems.iter().position(|&e| e == elem) {
            self.elems.remove(i);
            true
        } else {
            false
        }
    }

    fn to_dense(&self) -> BitSet<T> {
        let mut dense = BitSet::new_empty(self.domain_size);
        for elem in self.elems.iter() {
            dense.insert(*elem);
        }
        dense
    }

    fn iter(&self) -> slice::Iter<'_, T> {
        self.elems.iter()
    }
}

impl<T: Idx + Ord> SparseBitSet<T> {
    fn last_set_in(&self, range: impl RangeBounds<T>) -> Option<T> {
        let mut last_leq = None;
        for e in self.iter() {
            if range.contains(e) {
                last_leq = Some(*e);
            }
        }
        last_leq
    }
}

/// A fixed-size bitset type with a hybrid representation: sparse when there
/// are up to a `SPARSE_MAX` elements in the set, but dense when there are more
/// than `SPARSE_MAX`.
///
/// This type is especially efficient for sets that typically have a small
/// number of elements, but a large `domain_size`, and are cleared frequently.
///
/// `T` is an index type, typically a newtyped `usize` wrapper, but it can also
/// just be `usize`.
///
/// All operations that involve an element will panic if the element is equal
/// to or greater than the domain size. All operations that involve two bitsets
/// will panic if the bitsets have differing domain sizes.
#[derive(Clone)]
pub enum HybridBitSet<T> {
    Sparse(SparseBitSet<T>),
    Dense(BitSet<T>),
}

impl<T: Idx> fmt::Debug for HybridBitSet<T> {
    fn fmt(&self, w: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Sparse(b) => b.fmt(w),
            Self::Dense(b) => b.fmt(w),
        }
    }
}

impl<T: Idx> HybridBitSet<T> {
    bit_relations_inherent_impls! {}

    pub fn new_empty(domain_size: usize) -> Self {
        HybridBitSet::Sparse(SparseBitSet::new_empty(domain_size))
    }

    pub fn from_dense(dense: &DenseBitSet<T>) -> Self {
        HybridBitSet::Dense(BitSet::from_dense(dense))
    }

    pub fn domain_size(&self) -> usize {
        match self {
            HybridBitSet::Sparse(sparse) => sparse.domain_size,
            HybridBitSet::Dense(dense) => dense.domain_size,
        }
    }

    pub fn clear(&mut self) {
        let domain_size = self.domain_size();
        *self = HybridBitSet::new_empty(domain_size);
    }

    pub fn contains(&self, elem: T) -> bool {
        match self {
            HybridBitSet::Sparse(sparse) => sparse.contains(elem),
            HybridBitSet::Dense(dense) => dense.contains(elem),
        }
    }

    pub fn superset(&self, other: &HybridBitSet<T>) -> bool {
        match (self, other) {
            (HybridBitSet::Dense(self_dense), HybridBitSet::Dense(other_dense)) => {
                self_dense.superset(other_dense)
            }
            _ => {
                assert!(self.domain_size() == other.domain_size());
                other.iter().all(|elem| self.contains(elem))
            }
        }
    }

    pub fn is_empty(&self) -> bool {
        match self {
            HybridBitSet::Sparse(sparse) => sparse.is_empty(),
            HybridBitSet::Dense(dense) => dense.is_empty(),
        }
    }

    /// Returns the previous element present in the bitset from `elem`,
    /// inclusively of elem. That is, will return `Some(elem)` if elem is in the
    /// bitset.
    pub fn last_set_in(&self, range: impl RangeBounds<T>) -> Option<T>
    where T: Ord {
        match self {
            HybridBitSet::Sparse(sparse) => sparse.last_set_in(range),
            HybridBitSet::Dense(dense) => dense.last_set_in(range),
        }
    }

    pub fn insert(&mut self, elem: T) -> bool {
        // No need to check `elem` against `self.domain_size` here because all
        // the match cases check it, one way or another.
        match self {
            HybridBitSet::Sparse(sparse) if sparse.len() < SPARSE_MAX => {
                // The set is sparse and has space for `elem`.
                sparse.insert(elem)
            }
            HybridBitSet::Sparse(sparse) if sparse.contains(elem) => {
                // The set is sparse and does not have space for `elem`, but
                // that doesn't matter because `elem` is already present.
                false
            }
            HybridBitSet::Sparse(sparse) => {
                // The set is sparse and full. Convert to a dense set.
                let mut dense = sparse.to_dense();
                let changed = dense.insert(elem);
                assert!(changed);
                *self = HybridBitSet::Dense(dense);
                changed
            }
            HybridBitSet::Dense(dense) => dense.insert(elem),
        }
    }

    pub fn insert_range(&mut self, elems: impl RangeBounds<T>) {
        // No need to check `elem` against `self.domain_size` here because all
        // the match cases check it, one way or another.
        let start = match elems.start_bound().cloned() {
            Bound::Included(start) => start.index(),
            Bound::Excluded(start) => start.index() + 1,
            Bound::Unbounded => 0,
        };
        let end = match elems.end_bound().cloned() {
            Bound::Included(end) => end.index() + 1,
            Bound::Excluded(end) => end.index(),
            Bound::Unbounded => self.domain_size() - 1,
        };
        let Some(len) = end.checked_sub(start) else {
            return;
        };
        match self {
            HybridBitSet::Sparse(sparse) if sparse.len() + len < SPARSE_MAX => {
                // The set is sparse and has space for `elems`.
                for elem in start..end {
                    sparse.insert(T::new(elem));
                }
            }
            HybridBitSet::Sparse(sparse) => {
                // The set is sparse and full. Convert to a dense set.
                let mut dense = sparse.to_dense();
                dense.insert_range(elems);
                *self = HybridBitSet::Dense(dense);
            }
            HybridBitSet::Dense(dense) => dense.insert_range(elems),
        }
    }

    pub fn insert_all(&mut self) {
        let domain_size = self.domain_size();
        match self {
            HybridBitSet::Sparse(_) => {
                *self = HybridBitSet::Dense(BitSet::new_filled(domain_size));
            }
            HybridBitSet::Dense(dense) => dense.insert_all(),
        }
    }

    pub fn remove(&mut self, elem: T) -> bool {
        // Note: we currently don't bother going from Dense back to Sparse.
        match self {
            HybridBitSet::Sparse(sparse) => sparse.remove(elem),
            HybridBitSet::Dense(dense) => dense.remove(elem),
        }
    }

    /// Converts to a dense set, consuming itself in the process.
    pub fn to_dense(self) -> BitSet<T> {
        match self {
            HybridBitSet::Sparse(sparse) => sparse.to_dense(),
            HybridBitSet::Dense(dense) => dense,
        }
    }

    pub fn iter(&self) -> HybridIter<'_, T> {
        match self {
            HybridBitSet::Sparse(sparse) => HybridIter::Sparse(sparse.iter()),
            HybridBitSet::Dense(dense) => HybridIter::Dense(dense.iter()),
        }
    }
}

#[derive(Debug)]
pub enum HybridIter<'a, T: Idx> {
    Sparse(slice::Iter<'a, T>),
    Dense(BitIter<'a, T>),
}

impl<T: Idx> Iterator for HybridIter<'_, T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        match self {
            HybridIter::Sparse(sparse) => sparse.next().copied(),
            HybridIter::Dense(dense) => dense.next(),
        }
    }
}

#[inline]
fn num_words<T: Idx>(domain_size: T) -> usize {
    domain_size.index().div_ceil(WORD_BITS)
}

#[inline]
fn word_index_and_mask<T: Idx>(elem: T) -> (usize, Word) {
    let elem = elem.index();
    let word_index = elem / WORD_BITS;
    let mask = 1 << (elem % WORD_BITS);
    (word_index, mask)
}

fn clear_excess_bits_in_final_word(domain_size: usize, words: &mut [Word]) {
    let num_bits_in_final_word = domain_size % WORD_BITS;
    if num_bits_in_final_word > 0 {
        let mask = (1 << num_bits_in_final_word) - 1;
        words[words.len() - 1] &= mask;
    }
}

#[inline]
fn max_bit(word: Word) -> usize {
    WORD_BITS - 1 - word.leading_zeros() as usize
}
