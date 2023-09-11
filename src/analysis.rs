use std::{
    collections::{BTreeMap, BTreeSet},
    ops::Deref,
    path::Path,
};

use rustc_abi::VariantIdx;
use rustc_hir::ItemKind;
use rustc_middle::{
    mir::{
        visit::Visitor, BasicBlock, BasicBlockData, Body, CallReturnPlaces, Location, Place,
        ProjectionElem, Rvalue, Statement, StatementKind, Terminator, TerminatorEdges,
        TerminatorKind,
    },
    ty::{Ty, TyCtxt, TyKind},
};
use rustc_mir_dataflow::{
    fmt::DebugWithContext, lattice::JoinSemiLattice, Analysis, AnalysisDomain, Backward, Forward,
    GenKill, Results, ResultsVisitor,
};
use rustc_session::config::Input;

use crate::compile_util;

pub fn run_path(path: &Path) {
    analyze(compile_util::path_to_input(path));
}

pub fn run_code(code: &str) {
    analyze(compile_util::str_to_input(code));
}

fn analyze(input: Input) {
    let config = compile_util::make_config(input);
    compile_util::run_compiler(config, |source_map, tcx| {
        let hir = tcx.hir();
        for id in hir.items() {
            let item = hir.item(id);

            let params = if let ItemKind::Fn(sig, _, _) = &item.kind {
                sig.decl.inputs.len()
            } else {
                continue;
            };

            let def_id = item.item_id().owner_id.def_id.to_def_id();
            let body = tcx.optimized_mir(def_id);

            let mut param_tys = BTreeMap::new();
            for (i, local) in body.local_decls.iter().enumerate() {
                if i == 0 {
                    continue;
                }
                if i > params {
                    break;
                }
                if let TyKind::RawPtr(tm) = local.ty.kind() {
                    param_tys.insert(i, Type::from_ty(&tm.ty, tcx));
                }
            }

            let ctxt = Ctxt::new(params, param_tys);

            let mut visitor = WriteVisitor::new(ctxt.clone());
            visitor.visit_body(body);
            let mut writes = visitor.places;

            let results = ReadAnalysis::new(ctxt.clone())
                .into_engine(tcx, body)
                .iterate_to_fixpoint();
            let mut cursor = results.into_results_cursor(body);
            cursor.seek_to_block_start(BasicBlock::from_usize(0));
            let reads = &cursor.get().0;

            writes.retain(|place| {
                let local = place.local();
                0 < local && local <= params && !reads.contains(place)
            });

            if writes.is_empty() {
                continue;
            }

            let mut results = WriteAnalysis::new(ctxt)
                .into_engine(tcx, body)
                .iterate_to_fixpoint();
            let mut visitor = ReturnVisitor::new();
            results.visit_reachable_with(body, &mut visitor);
            let mut must_writes = visitor
                .0
                .unwrap_or_else(MustPlaceSet::top)
                .into_set()
                .unwrap();
            must_writes.retain(|place| writes.contains(place));

            let mut may_writes = writes;
            may_writes.retain(|place| !must_writes.contains(place));

            let file = compile_util::span_to_path(item.span, source_map);
            let name = item.ident.name.to_ident_string();
            println!(
                "{} {} {:?} {:?}",
                file.unwrap_or_default().as_os_str().to_str().unwrap(),
                name,
                must_writes,
                may_writes
            );
        }
    });
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Type {
    Struct(BTreeMap<usize, Type>),
    NonStruct,
}

impl Type {
    fn from_ty<'tcx>(ty: &Ty<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        if let TyKind::Adt(adt_def, generic_args) = ty.kind() {
            if adt_def.is_struct() {
                let variant = adt_def.variant(VariantIdx::from_usize(0));
                return Self::Struct(
                    variant
                        .fields
                        .iter()
                        .enumerate()
                        .map(|(i, field)| (i, Self::from_ty(&field.ty(tcx, generic_args), tcx)))
                        .collect(),
                );
            }
        }
        Self::NonStruct
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
struct PlacePath(Vec<usize>);

impl PlacePath {
    fn local(&self) -> usize {
        self.0[0]
    }

    fn from_place(place: &Place<'_>) -> (Self, bool) {
        let mut projections = vec![place.local.index()];
        let mut array_access = false;
        for proj in place.projection.iter() {
            match proj {
                ProjectionElem::Deref => {}
                ProjectionElem::Field(idx, _) => projections.push(idx.index()),
                ProjectionElem::Index(_) => {
                    array_access = true;
                    break;
                }
                _ => panic!("{:?}", place),
            }
        }
        (Self(projections), array_access)
    }
}

impl std::fmt::Debug for PlacePath {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, n) in self.0.iter().enumerate() {
            if i == 0 {
                write!(f, "{}", n)?;
            } else {
                write!(f, ".{}", n)?;
            }
        }
        Ok(())
    }
}

fn expands_path(
    path: &[usize],
    tys: &BTreeMap<usize, Type>,
    mut curr: Vec<usize>,
) -> Vec<Vec<usize>> {
    if let Some(first) = path.first() {
        curr.push(*first);
        if let Type::Struct(fields) = tys.get(first).unwrap() {
            expands_path(&path[1..], fields, curr)
        } else {
            vec![curr]
        }
    } else {
        tys.iter()
            .flat_map(|(n, ty)| {
                let mut curr = curr.clone();
                curr.push(*n);
                if let Type::Struct(fields) = ty {
                    expands_path(path, fields, curr)
                } else {
                    vec![curr]
                }
            })
            .collect()
    }
}

#[derive(Debug, Clone)]
struct Ctxt {
    params: usize,
    param_tys: BTreeMap<usize, Type>,
}

impl Ctxt {
    fn new(params: usize, param_tys: BTreeMap<usize, Type>) -> Self {
        Self { params, param_tys }
    }

    fn is_ptr_param(&self, place: &Place<'_>) -> bool {
        (1..=self.params).contains(&place.local.index()) && place.is_indirect_first_projection()
    }

    fn expands_path(&self, place: &PlacePath) -> Vec<PlacePath> {
        expands_path(&place.0, &self.param_tys, vec![])
            .into_iter()
            .map(PlacePath)
            .collect()
    }
}

struct WriteVisitor {
    ctxt: Ctxt,
    places: BTreeSet<PlacePath>,
}

impl WriteVisitor {
    fn new(ctxt: Ctxt) -> Self {
        Self {
            ctxt,
            places: BTreeSet::new(),
        }
    }
}

impl<'tcx> Visitor<'tcx> for WriteVisitor {
    fn visit_assign(&mut self, place: &Place<'tcx>, rvalue: &Rvalue<'tcx>, location: Location) {
        if self.ctxt.is_ptr_param(place) {
            let (place, is_read) = PlacePath::from_place(place);
            if !is_read {
                for place in self.ctxt.expands_path(&place) {
                    self.places.insert(place);
                }
            }
        }
        self.super_assign(place, rvalue, location);
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct MayPlaceSet(BTreeSet<PlacePath>);

impl MayPlaceSet {
    fn bottom() -> Self {
        Self(BTreeSet::new())
    }
}

impl JoinSemiLattice for MayPlaceSet {
    fn join(&mut self, other: &Self) -> bool {
        let mut b = false;
        for place in &other.0 {
            b |= self.0.insert(place.clone());
        }
        b
    }
}

impl GenKill<PlacePath> for MayPlaceSet {
    fn gen(&mut self, place: PlacePath) {
        self.0.insert(place);
    }

    fn kill(&mut self, place: PlacePath) {
        self.0.remove(&place);
    }
}

impl<T> DebugWithContext<T> for MayPlaceSet {}

#[derive(Debug, Clone, PartialEq, Eq)]
enum MustPlaceSet {
    All,
    Set(BTreeSet<PlacePath>),
}

impl MustPlaceSet {
    fn bottom() -> Self {
        Self::All
    }

    fn top() -> Self {
        Self::Set(BTreeSet::new())
    }

    fn into_set(self) -> Option<BTreeSet<PlacePath>> {
        match self {
            Self::All => None,
            Self::Set(set) => Some(set),
        }
    }
}

impl JoinSemiLattice for MustPlaceSet {
    fn join(&mut self, other: &Self) -> bool {
        match (&mut *self, other) {
            (_, Self::All) => false,
            (Self::All, _) => {
                *self = other.clone();
                true
            }
            (Self::Set(s1), Self::Set(s2)) => {
                let len = s1.len();
                s1.retain(|p| s2.contains(p));
                s1.len() < len
            }
        }
    }
}

impl GenKill<PlacePath> for MustPlaceSet {
    fn gen(&mut self, place: PlacePath) {
        if let Self::Set(set) = self {
            set.insert(place);
        }
    }

    fn kill(&mut self, place: PlacePath) {
        if let Self::Set(set) = self {
            set.remove(&place);
        }
    }
}

impl<T> DebugWithContext<T> for MustPlaceSet {}

struct ReadAnalysis {
    ctxt: Ctxt,
}

impl ReadAnalysis {
    fn new(ctxt: Ctxt) -> Self {
        Self { ctxt }
    }
}

impl<'tcx> AnalysisDomain<'tcx> for ReadAnalysis {
    type Direction = Backward;
    type Domain = MayPlaceSet;

    const NAME: &'static str = "read_before_write";

    fn bottom_value(&self, _: &Body<'tcx>) -> Self::Domain {
        MayPlaceSet::bottom()
    }

    fn initialize_start_block(&self, _: &Body<'tcx>, _: &mut Self::Domain) {}
}

impl<'tcx> Analysis<'tcx> for ReadAnalysis {
    fn apply_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        _: Location,
    ) {
        if let StatementKind::Assign(place_rvalue) = &statement.kind {
            let (place, rvalue) = place_rvalue.deref();
            if self.ctxt.is_ptr_param(place) {
                let (place, is_read) = PlacePath::from_place(place);
                let places = self.ctxt.expands_path(&place);
                if is_read {
                    state.gen_all(places);
                } else {
                    state.kill_all(places);
                }
            }
            for place in rvalue_to_places(rvalue) {
                if self.ctxt.is_ptr_param(&place) {
                    state.gen_all(self.ctxt.expands_path(&PlacePath::from_place(&place).0));
                }
            }
        }
    }

    fn apply_terminator_effect<'mir>(
        &mut self,
        _: &mut Self::Domain,
        terminator: &'mir Terminator<'tcx>,
        _: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        terminator.edges()
    }

    fn apply_call_return_effect(
        &mut self,
        _: &mut Self::Domain,
        _: BasicBlock,
        _: CallReturnPlaces<'_, '_>,
    ) {
    }
}

struct WriteAnalysis {
    ctxt: Ctxt,
}

impl WriteAnalysis {
    fn new(ctxt: Ctxt) -> Self {
        Self { ctxt }
    }
}

impl<'tcx> AnalysisDomain<'tcx> for WriteAnalysis {
    type Direction = Forward;
    type Domain = MustPlaceSet;

    const NAME: &'static str = "read_before_write";

    fn bottom_value(&self, _: &Body<'tcx>) -> Self::Domain {
        MustPlaceSet::bottom()
    }

    fn initialize_start_block(&self, _: &Body<'tcx>, state: &mut Self::Domain) {
        *state = MustPlaceSet::top();
    }
}

impl<'tcx> Analysis<'tcx> for WriteAnalysis {
    fn apply_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        _: Location,
    ) {
        if let StatementKind::Assign(place_rvalue) = &statement.kind {
            let (place, _) = place_rvalue.deref();
            if self.ctxt.is_ptr_param(place) {
                let (place, is_read) = PlacePath::from_place(place);
                if !is_read {
                    state.gen_all(self.ctxt.expands_path(&place));
                }
            }
        }
    }

    fn apply_terminator_effect<'mir>(
        &mut self,
        _: &mut Self::Domain,
        terminator: &'mir Terminator<'tcx>,
        _: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        terminator.edges()
    }

    fn apply_call_return_effect(
        &mut self,
        _: &mut Self::Domain,
        _: BasicBlock,
        _: CallReturnPlaces<'_, '_>,
    ) {
    }
}

fn rvalue_to_places<'tcx>(rvalue: &Rvalue<'tcx>) -> Vec<Place<'tcx>> {
    let mut places = vec![];
    let mut add_opt = |opt: Option<Place<'tcx>>| {
        if let Some(place) = opt {
            places.push(place);
        }
    };
    match rvalue {
        Rvalue::Use(o)
        | Rvalue::Repeat(o, _)
        | Rvalue::Cast(_, o, _)
        | Rvalue::UnaryOp(_, o)
        | Rvalue::ShallowInitBox(o, _) => add_opt(o.place()),
        Rvalue::BinaryOp(_, os) | Rvalue::CheckedBinaryOp(_, os) => {
            let (o1, o2) = os.deref();
            add_opt(o1.place());
            add_opt(o2.place());
        }
        Rvalue::Aggregate(_, os) => {
            for o in os {
                add_opt(o.place());
            }
        }
        Rvalue::CopyForDeref(p) => add_opt(Some(*p)),
        Rvalue::Ref(_, _, _)
        | Rvalue::ThreadLocalRef(_)
        | Rvalue::AddressOf(_, _)
        | Rvalue::Len(_)
        | Rvalue::NullaryOp(_, _)
        | Rvalue::Discriminant(_) => {}
    }
    places
}

struct ReturnVisitor<'tcx, A: Analysis<'tcx>>(Option<A::Domain>);

impl<'tcx, A: Analysis<'tcx>> ReturnVisitor<'tcx, A> {
    fn new() -> Self {
        Self(None)
    }
}

impl<'mir, 'tcx, A: Analysis<'tcx>> ResultsVisitor<'mir, 'tcx, Results<'tcx, A>>
    for ReturnVisitor<'tcx, A>
{
    type FlowState = A::Domain;

    fn visit_terminator_before_primary_effect(
        &mut self,
        _: &Results<'tcx, A>,
        state: &Self::FlowState,
        terminator: &'mir Terminator<'tcx>,
        _: Location,
    ) {
        if matches!(&terminator.kind, TerminatorKind::Return) {
            self.0 = Some(state.clone());
        }
    }
}

struct DebugVisitor;

impl<'mir, 'tcx, D: std::fmt::Debug, A: Analysis<'tcx, Domain = D>>
    ResultsVisitor<'mir, 'tcx, Results<'tcx, A>> for DebugVisitor
{
    type FlowState = D;

    fn visit_block_start(
        &mut self,
        _: &Results<'tcx, A>,
        _: &Self::FlowState,
        _: &'mir BasicBlockData<'tcx>,
        block: BasicBlock,
    ) {
        println!("Block {} starts", block.index());
    }

    fn visit_statement_before_primary_effect(
        &mut self,
        _: &Results<'tcx, A>,
        state: &Self::FlowState,
        statement: &'mir Statement<'tcx>,
        _: Location,
    ) {
        println!("In:  {:?}", state);
        println!("{:?}", statement);
    }

    fn visit_statement_after_primary_effect(
        &mut self,
        _: &Results<'tcx, A>,
        state: &Self::FlowState,
        _: &'mir Statement<'tcx>,
        _: Location,
    ) {
        println!("Out: {:?}", state);
    }

    fn visit_terminator_before_primary_effect(
        &mut self,
        _: &Results<'tcx, A>,
        state: &Self::FlowState,
        terminator: &'mir Terminator<'tcx>,
        _: Location,
    ) {
        println!("In:  {:?}", state);
        println!("{:?}", terminator);
    }

    fn visit_terminator_after_primary_effect(
        &mut self,
        _: &Results<'tcx, A>,
        state: &Self::FlowState,
        _: &'mir Terminator<'tcx>,
        _: Location,
    ) {
        println!("Out: {:?}", state);
    }

    fn visit_block_end(
        &mut self,
        _: &Results<'tcx, A>,
        _: &Self::FlowState,
        _: &'mir BasicBlockData<'tcx>,
        block: BasicBlock,
    ) {
        println!("Block {} ends", block.index());
    }
}
