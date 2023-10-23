use std::collections::{BTreeMap, BTreeSet};

use rustc_data_structures::graph::{scc::Sccs, vec_graph::VecGraph};
use rustc_index::Idx;

pub fn transitive_closure<T: Idx + Ord>(
    graph: &BTreeMap<T, BTreeSet<T>>,
) -> BTreeMap<T, BTreeSet<T>> {
    let len = graph.len();

    let mut reachability = vec![vec![false; len]; len];
    for (v, succs) in graph.iter() {
        for succ in succs {
            reachability[v.index()][succ.index()] = true;
        }
    }

    for k in 0..len {
        for i in 0..len {
            for j in 0..len {
                reachability[i][j] =
                    reachability[i][j] || (reachability[i][k] && reachability[k][j]);
            }
        }
    }

    let mut new_graph = BTreeMap::new();
    for (i, reachability) in reachability.iter().enumerate() {
        let neighbors = reachability
            .iter()
            .enumerate()
            .filter_map(|(to, is_reachable)| {
                if *is_reachable {
                    Some(T::new(to))
                } else {
                    None
                }
            })
            .collect();
        new_graph.insert(T::new(i), neighbors);
    }
    new_graph
}

pub fn reachable_vertices<T: Idx + Ord>(
    graph: &BTreeMap<T, BTreeSet<T>>,
    source: T,
) -> BTreeSet<T> {
    let mut dists = vec![usize::MAX; graph.len()];
    dists[source.index()] = 0;

    let mut nodes = vec![];
    let mut heap = FibonacciHeap::new();
    for (i, dist) in dists.iter().cloned().enumerate() {
        nodes.push(heap.insert(i, dist));
    }

    while let Some(v) = heap.remove_min() {
        let v_dist = dists[v];
        if v_dist == usize::MAX {
            break;
        }
        for succ in &graph[&T::new(v)] {
            let succ = succ.index();
            let dist = v_dist + 1;
            if dist < dists[succ] {
                dists[succ] = dist;
                unsafe {
                    heap.decrease_key(nodes[succ], dist);
                }
            }
        }
    }

    dists
        .into_iter()
        .enumerate()
        .filter_map(|(i, dist)| {
            if dist != usize::MAX {
                Some(T::new(i))
            } else {
                None
            }
        })
        .collect()
}

fn symmetric_closure<T: Clone + Eq + PartialOrd + Ord>(
    map: &BTreeMap<T, BTreeSet<T>>,
) -> BTreeMap<T, BTreeSet<T>> {
    let mut clo = map.clone();
    for (node, succs) in map {
        for succ in succs {
            clo.get_mut(succ).unwrap().insert(node.clone());
        }
    }
    clo
}

pub fn inverse<T: Clone + Eq + PartialOrd + Ord>(
    map: &BTreeMap<T, BTreeSet<T>>,
) -> BTreeMap<T, BTreeSet<T>> {
    let mut inv: BTreeMap<_, BTreeSet<_>> = BTreeMap::new();
    for node in map.keys() {
        inv.insert(node.clone(), BTreeSet::new());
    }
    for (node, succs) in map {
        for succ in succs {
            inv.get_mut(succ).unwrap().insert(node.clone());
        }
    }
    inv
}

/// `map` must not have a cycle.
pub fn post_order<T: Clone + Eq + PartialOrd + Ord>(
    map: &BTreeMap<T, BTreeSet<T>>,
    inv_map: &BTreeMap<T, BTreeSet<T>>,
) -> Vec<Vec<T>> {
    let mut res = vec![];
    let clo = symmetric_closure(map);
    let (_, components) = compute_sccs(&clo);

    for (_, component) in components {
        let mut v = vec![];
        let mut reached = BTreeSet::new();
        for node in component {
            if inv_map.get(&node).unwrap().is_empty() {
                dfs_walk(&node, &mut v, &mut reached, map);
            }
        }
        res.push(v);
    }

    res
}

fn dfs_walk<T: Clone + Eq + PartialOrd + Ord>(
    node: &T,
    v: &mut Vec<T>,
    reached: &mut BTreeSet<T>,
    map: &BTreeMap<T, BTreeSet<T>>,
) {
    reached.insert(node.clone());
    for succ in map.get(node).unwrap() {
        if !reached.contains(succ) {
            dfs_walk(succ, v, reached, map);
        }
    }
    v.push(node.clone());
}

pub fn compute_sccs<T: Clone + Eq + PartialOrd + Ord>(
    map: &BTreeMap<T, BTreeSet<T>>,
) -> (BTreeMap<Id, BTreeSet<Id>>, BTreeMap<Id, BTreeSet<T>>) {
    let id_map: BTreeMap<_, _> = map
        .keys()
        .enumerate()
        .map(|(i, f)| (i, f.clone()))
        .collect();
    let inv_id_map: BTreeMap<_, _> = id_map.iter().map(|(i, f)| (f.clone(), *i)).collect();
    let edges = map
        .iter()
        .flat_map(|(node, succs)| {
            succs.iter().map(|succ| {
                (
                    Id::new(*inv_id_map.get(node).unwrap()),
                    Id::new(*inv_id_map.get(succ).unwrap()),
                )
            })
        })
        .collect();
    let sccs: Sccs<Id, Id> = Sccs::new(&VecGraph::new(map.len(), edges));

    let component_graph: BTreeMap<_, _> = sccs
        .all_sccs()
        .map(|node| (node, sccs.successors(node).iter().cloned().collect()))
        .collect();

    let mut component_elems: BTreeMap<_, BTreeSet<_>> = BTreeMap::new();
    for i in 0..(map.len()) {
        let scc = sccs.scc(Id::new(i));
        let node = id_map.get(&i).unwrap().clone();
        component_elems.entry(scc).or_default().insert(node);
    }

    (component_graph, component_elems)
}

#[derive(Clone, Copy, Eq, PartialEq, Debug, Hash, PartialOrd, Ord)]
#[repr(transparent)]
pub struct Id(usize);

impl Idx for Id {
    fn new(idx: usize) -> Self {
        Self(idx)
    }

    fn index(self) -> usize {
        self.0
    }
}

struct Node<V, K> {
    v: V,
    k: K,
    degree: usize,
    mark: bool,
    parent: *mut Node<V, K>,
    left: *mut Node<V, K>,
    right: *mut Node<V, K>,
    children: *mut Node<V, K>,
}

impl<V, K> Node<V, K> {
    fn new(v: V, k: K) -> *mut Self {
        let node = Self {
            v,
            k,
            degree: 0,
            mark: false,
            parent: std::ptr::null_mut(),
            left: std::ptr::null_mut(),
            right: std::ptr::null_mut(),
            children: std::ptr::null_mut(),
        };
        Box::into_raw(Box::new(node))
    }

    unsafe fn make_list(this: *mut Self) {
        unsafe {
            (*this).left = this;
            (*this).right = this;
        }
    }

    unsafe fn insert(this: *mut Self, node: *mut Self) {
        unsafe {
            (*node).left = (*this).left;
            (*(*this).left).right = node;
            (*this).left = node;
            (*node).right = this;
        }
    }

    unsafe fn remove(this: *mut Self) {
        unsafe {
            (*(*this).left).right = (*this).right;
            (*(*this).right).left = (*this).left;
        }
    }

    fn free(&mut self) {
        let mut x = self.children;
        if x.is_null() {
            return;
        }
        loop {
            let mut node = unsafe { Box::from_raw(x) };
            x = node.right;
            node.free();
            if x == self.children {
                break;
            }
        }
    }
}

struct FibonacciHeap<V, K> {
    min: *mut Node<V, K>,
    n: usize,
}

impl<V, K> Drop for FibonacciHeap<V, K> {
    fn drop(&mut self) {
        let mut x = self.min;
        if x.is_null() {
            return;
        }
        loop {
            let mut node = unsafe { Box::from_raw(x) };
            x = node.right;
            node.free();
            if x == self.min {
                break;
            }
        }
    }
}

impl<V, K: Ord + Copy> FibonacciHeap<V, K> {
    fn new() -> Self {
        Self {
            min: std::ptr::null_mut(),
            n: 0,
        }
    }

    fn insert(&mut self, v: V, k: K) -> *mut Node<V, K> {
        let node = Node::new(v, k);
        if self.min.is_null() {
            unsafe {
                Node::make_list(node);
            }
            self.min = node;
        } else {
            unsafe {
                Node::insert(self.min, node);
            }
            if k < unsafe { (*self.min).k } {
                self.min = node;
            }
        }
        self.n += 1;
        node
    }

    fn remove_min(&mut self) -> Option<V> {
        if self.min.is_null() {
            return None;
        }
        let z = self.min;
        let v = unsafe {
            let mut x = (*z).children;
            if !x.is_null() {
                loop {
                    let next = (*x).right;
                    Node::insert(self.min, x);
                    (*x).parent = std::ptr::null_mut();
                    x = next;
                    if x == (*z).children {
                        break;
                    }
                }
            }
            Node::remove(z);
            if z == (*z).right {
                self.min = std::ptr::null_mut();
            } else {
                self.min = (*z).right;
                self.consolidate();
            }
            Box::into_inner(Box::from_raw(z)).v
        };
        self.n -= 1;
        Some(v)
    }

    fn consolidate(&mut self) {
        let dn = (self.n as f64).log(1.61803).ceil() as usize;
        let mut arr = vec![std::ptr::null_mut::<Node<V, K>>(); dn];
        let mut w = self.min;
        let last = unsafe { (*w).left };
        loop {
            unsafe {
                let next = (*w).right;
                let mut x = w;
                let mut d = (*x).degree;
                while !arr[d].is_null() {
                    let mut y = arr[d];
                    if (*x).k > (*y).k {
                        std::mem::swap(&mut x, &mut y);
                    }
                    self.link(y, x);
                    arr[d] = std::ptr::null_mut();
                    d += 1;
                }
                arr[d] = x;
                if w == last {
                    break;
                }
                w = next;
            }
        }
        self.min = std::ptr::null_mut();
        for x in arr {
            if x.is_null() {
                continue;
            }
            if self.min.is_null() {
                unsafe {
                    Node::make_list(x);
                }
                self.min = x;
            } else {
                unsafe {
                    Node::insert(self.min, x);
                    if (*x).k < (*self.min).k {
                        self.min = x;
                    }
                }
            }
        }
    }

    unsafe fn link(&mut self, y: *mut Node<V, K>, x: *mut Node<V, K>) {
        unsafe {
            Node::remove(y);
            if (*x).children.is_null() {
                (*x).children = y;
                Node::make_list(y);
            } else {
                Node::insert((*x).children, y);
            }
            (*y).parent = x;
            (*y).mark = false;
            (*x).degree += 1;
        }
    }

    unsafe fn decrease_key(&mut self, x: *mut Node<V, K>, k: K) {
        unsafe {
            assert!(k < (*x).k);
            (*x).k = k;
            let y = (*x).parent;
            if !y.is_null() && (*x).k < (*y).k {
                self.cut(x, y);
                self.cascading_cut(y);
            }
            if (*x).k < (*self.min).k {
                self.min = x;
            }
        }
    }

    unsafe fn cut(&mut self, x: *mut Node<V, K>, y: *mut Node<V, K>) {
        unsafe {
            Node::remove(x);
            if x == (*x).right {
                (*y).children = std::ptr::null_mut();
            } else {
                (*y).children = (*x).right;
            }
            Node::insert(self.min, x);
            (*y).degree -= 1;
            (*x).parent = std::ptr::null_mut();
            (*x).mark = false;
        }
    }

    unsafe fn cascading_cut(&mut self, y: *mut Node<V, K>) {
        unsafe {
            let z = (*y).parent;
            if z.is_null() {
                return;
            }
            if !(*y).mark {
                (*y).mark = true;
            } else {
                self.cut(y, z);
                self.cascading_cut(z);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fibonacci_heap_1() {
        let n = 1000000;
        let mut heap = FibonacciHeap::new();
        for i in 0..n {
            heap.insert(i, i);
        }
        for i in 0..n {
            let j = heap.remove_min().unwrap();
            assert_eq!(i, j);
        }
    }

    #[test]
    fn test_fibonacci_heap_2() {
        let n = 1000000;
        let mut heap = FibonacciHeap::new();
        let mut v = vec![];
        for i in 0..n {
            v.push(heap.insert(i, n + i));
        }
        for i in (0..n).rev() {
            unsafe { heap.decrease_key(v[i], i) };
        }
        for i in 0..n {
            let j = heap.remove_min().unwrap();
            assert_eq!(i, j);
        }
    }

    #[test]
    fn test_fibonacci_heap_3() {
        let n = 1000000;
        let mut heap = FibonacciHeap::new();
        let mut v = vec![];
        for i in 0..n {
            v.push(heap.insert(i, n + i));
        }
        for i in (0..n).rev() {
            unsafe { heap.decrease_key(v[i], i) };
            let j = heap.remove_min().unwrap();
            assert_eq!(i, j);
        }
    }

    const I0: Id = Id(0);
    const I1: Id = Id(1);
    const I2: Id = Id(2);
    const I3: Id = Id(3);
    const I4: Id = Id(4);
    const I5: Id = Id(5);

    #[test]
    fn test_reachability_1() {
        let mut graph = BTreeMap::new();
        graph.insert(I0, BTreeSet::from_iter(vec![I1]));
        graph.insert(I1, BTreeSet::from_iter(vec![I2]));
        graph.insert(I2, BTreeSet::from_iter(vec![I3]));
        graph.insert(I3, BTreeSet::from_iter(vec![I4]));
        graph.insert(I4, BTreeSet::from_iter(vec![]));

        let transitive_closure_graph = transitive_closure(&graph);
        let mut expected = BTreeMap::new();
        expected.insert(I0, BTreeSet::from_iter(vec![I1, I2, I3, I4]));
        expected.insert(I1, BTreeSet::from_iter(vec![I2, I3, I4]));
        expected.insert(I2, BTreeSet::from_iter(vec![I3, I4]));
        expected.insert(I3, BTreeSet::from_iter(vec![I4]));
        expected.insert(I4, BTreeSet::from_iter(vec![]));
        assert_eq!(transitive_closure_graph, expected);

        let reachables = reachable_vertices(&graph, I0);
        let expected = BTreeSet::from_iter(vec![I0, I1, I2, I3, I4]);
        assert_eq!(reachables, expected);

        let reachables = reachable_vertices(&graph, I1);
        let expected = BTreeSet::from_iter(vec![I1, I2, I3, I4]);
        assert_eq!(reachables, expected);

        let reachables = reachable_vertices(&graph, I2);
        let expected = BTreeSet::from_iter(vec![I2, I3, I4]);
        assert_eq!(reachables, expected);

        let reachables = reachable_vertices(&graph, I3);
        let expected = BTreeSet::from_iter(vec![I3, I4]);
        assert_eq!(reachables, expected);

        let reachables = reachable_vertices(&graph, I4);
        let expected = BTreeSet::from_iter(vec![I4]);
        assert_eq!(reachables, expected);
    }

    #[test]
    fn test_reachability_2() {
        let mut graph = BTreeMap::new();
        graph.insert(I0, BTreeSet::from_iter(vec![I1]));
        graph.insert(I1, BTreeSet::from_iter(vec![I2, I3]));
        graph.insert(I2, BTreeSet::from_iter(vec![I1]));
        graph.insert(I3, BTreeSet::from_iter(vec![I4]));
        graph.insert(I4, BTreeSet::from_iter(vec![]));

        let transitive_closure_graph = transitive_closure(&graph);
        let mut expected = BTreeMap::new();
        expected.insert(I0, BTreeSet::from_iter(vec![I1, I2, I3, I4]));
        expected.insert(I1, BTreeSet::from_iter(vec![I1, I2, I3, I4]));
        expected.insert(I2, BTreeSet::from_iter(vec![I1, I2, I3, I4]));
        expected.insert(I3, BTreeSet::from_iter(vec![I4]));
        expected.insert(I4, BTreeSet::from_iter(vec![]));
        assert_eq!(transitive_closure_graph, expected);

        let reachables = reachable_vertices(&graph, I0);
        let expected = BTreeSet::from_iter(vec![I0, I1, I2, I3, I4]);
        assert_eq!(reachables, expected);

        let reachables = reachable_vertices(&graph, I1);
        let expected = BTreeSet::from_iter(vec![I1, I2, I3, I4]);
        assert_eq!(reachables, expected);

        let reachables = reachable_vertices(&graph, I2);
        let expected = BTreeSet::from_iter(vec![I1, I2, I3, I4]);
        assert_eq!(reachables, expected);

        let reachables = reachable_vertices(&graph, I3);
        let expected = BTreeSet::from_iter(vec![I3, I4]);
        assert_eq!(reachables, expected);

        let reachables = reachable_vertices(&graph, I4);
        let expected = BTreeSet::from_iter(vec![I4]);
        assert_eq!(reachables, expected);
    }

    #[test]
    fn test_reachability_3() {
        let mut graph = BTreeMap::new();
        graph.insert(I0, BTreeSet::from_iter(vec![I1]));
        graph.insert(I1, BTreeSet::from_iter(vec![I1, I2]));
        graph.insert(I2, BTreeSet::from_iter(vec![I3]));
        graph.insert(I3, BTreeSet::from_iter(vec![I4]));
        graph.insert(I4, BTreeSet::from_iter(vec![]));

        let transitive_closure_graph = transitive_closure(&graph);
        let mut expected = BTreeMap::new();
        expected.insert(I0, BTreeSet::from_iter(vec![I1, I2, I3, I4]));
        expected.insert(I1, BTreeSet::from_iter(vec![I1, I2, I3, I4]));
        expected.insert(I2, BTreeSet::from_iter(vec![I3, I4]));
        expected.insert(I3, BTreeSet::from_iter(vec![I4]));
        expected.insert(I4, BTreeSet::from_iter(vec![]));
        assert_eq!(transitive_closure_graph, expected);

        let reachables = reachable_vertices(&graph, I0);
        let expected = BTreeSet::from_iter(vec![I0, I1, I2, I3, I4]);
        assert_eq!(reachables, expected);

        let reachables = reachable_vertices(&graph, I1);
        let expected = BTreeSet::from_iter(vec![I1, I2, I3, I4]);
        assert_eq!(reachables, expected);

        let reachables = reachable_vertices(&graph, I2);
        let expected = BTreeSet::from_iter(vec![I2, I3, I4]);
        assert_eq!(reachables, expected);

        let reachables = reachable_vertices(&graph, I3);
        let expected = BTreeSet::from_iter(vec![I3, I4]);
        assert_eq!(reachables, expected);

        let reachables = reachable_vertices(&graph, I4);
        let expected = BTreeSet::from_iter(vec![I4]);
        assert_eq!(reachables, expected);
    }

    #[test]
    fn test_reachability_4() {
        let mut graph = BTreeMap::new();
        graph.insert(I0, BTreeSet::from_iter(vec![I1, I3]));
        graph.insert(I1, BTreeSet::from_iter(vec![I2]));
        graph.insert(I2, BTreeSet::from_iter(vec![I1, I5]));
        graph.insert(I3, BTreeSet::from_iter(vec![I4]));
        graph.insert(I4, BTreeSet::from_iter(vec![I3, I5]));
        graph.insert(I5, BTreeSet::from_iter(vec![]));

        let transitive_closure_graph = transitive_closure(&graph);
        let mut expected = BTreeMap::new();
        expected.insert(I0, BTreeSet::from_iter(vec![I1, I2, I3, I4, I5]));
        expected.insert(I1, BTreeSet::from_iter(vec![I1, I2, I5]));
        expected.insert(I2, BTreeSet::from_iter(vec![I1, I2, I5]));
        expected.insert(I3, BTreeSet::from_iter(vec![I3, I4, I5]));
        expected.insert(I4, BTreeSet::from_iter(vec![I3, I4, I5]));
        expected.insert(I5, BTreeSet::from_iter(vec![]));
        assert_eq!(transitive_closure_graph, expected);

        let reachables = reachable_vertices(&graph, I0);
        let expected = BTreeSet::from_iter(vec![I0, I1, I2, I3, I4, I5]);
        assert_eq!(reachables, expected);

        let reachables = reachable_vertices(&graph, I1);
        let expected = BTreeSet::from_iter(vec![I1, I2, I5]);
        assert_eq!(reachables, expected);

        let reachables = reachable_vertices(&graph, I2);
        let expected = BTreeSet::from_iter(vec![I1, I2, I5]);
        assert_eq!(reachables, expected);

        let reachables = reachable_vertices(&graph, I3);
        let expected = BTreeSet::from_iter(vec![I3, I4, I5]);
        assert_eq!(reachables, expected);

        let reachables = reachable_vertices(&graph, I4);
        let expected = BTreeSet::from_iter(vec![I3, I4, I5]);
        assert_eq!(reachables, expected);

        let reachables = reachable_vertices(&graph, I5);
        let expected = BTreeSet::from_iter(vec![I5]);
        assert_eq!(reachables, expected);
    }

    #[test]
    fn test_reachability_5() {
        let mut graph = BTreeMap::new();
        graph.insert(I0, BTreeSet::from_iter(vec![I1]));
        graph.insert(I1, BTreeSet::from_iter(vec![I2]));
        graph.insert(I2, BTreeSet::from_iter(vec![I3, I4]));
        graph.insert(I3, BTreeSet::from_iter(vec![I3]));
        graph.insert(I4, BTreeSet::from_iter(vec![I1, I5]));
        graph.insert(I5, BTreeSet::from_iter(vec![]));

        let transitive_closure_graph = transitive_closure(&graph);
        let mut expected = BTreeMap::new();
        expected.insert(I0, BTreeSet::from_iter(vec![I1, I2, I3, I4, I5]));
        expected.insert(I1, BTreeSet::from_iter(vec![I1, I2, I3, I4, I5]));
        expected.insert(I2, BTreeSet::from_iter(vec![I1, I2, I3, I4, I5]));
        expected.insert(I3, BTreeSet::from_iter(vec![I3]));
        expected.insert(I4, BTreeSet::from_iter(vec![I1, I2, I3, I4, I5]));
        expected.insert(I5, BTreeSet::from_iter(vec![]));
        assert_eq!(transitive_closure_graph, expected);

        let reachables = reachable_vertices(&graph, I0);
        let expected = BTreeSet::from_iter(vec![I0, I1, I2, I3, I4, I5]);
        assert_eq!(reachables, expected);

        let reachables = reachable_vertices(&graph, I1);
        let expected = BTreeSet::from_iter(vec![I1, I2, I3, I4, I5]);
        assert_eq!(reachables, expected);

        let reachables = reachable_vertices(&graph, I2);
        let expected = BTreeSet::from_iter(vec![I1, I2, I3, I4, I5]);
        assert_eq!(reachables, expected);

        let reachables = reachable_vertices(&graph, I3);
        let expected = BTreeSet::from_iter(vec![I3]);
        assert_eq!(reachables, expected);

        let reachables = reachable_vertices(&graph, I4);
        let expected = BTreeSet::from_iter(vec![I1, I2, I3, I4, I5]);
        assert_eq!(reachables, expected);

        let reachables = reachable_vertices(&graph, I5);
        let expected = BTreeSet::from_iter(vec![I5]);
        assert_eq!(reachables, expected);
    }
}
