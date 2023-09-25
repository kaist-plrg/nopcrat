use std::collections::BTreeMap;

use rustc_hir::def_id::DefId;

use super::{analysis::*, domains::*};

mod arrays;
mod bools;
mod cast;
mod float;
mod fnptr;
mod int;
mod labels;
mod ptr;
mod structs;
mod uint;

fn analyze(code: &str) -> Vec<(Label, AbsState)> {
    let input = crate::compile_util::str_to_input(code);
    let config = crate::compile_util::make_config(input);
    crate::compile_util::run_compiler(config, |_, tcx| {
        let hir = tcx.hir();
        for id in hir.items() {
            let item = hir.item(id);
            let inputs = if let rustc_hir::ItemKind::Fn(sig, _, _) = &item.kind {
                sig.decl.inputs.len()
            } else {
                continue;
            };
            let def_id = item.item_id().owner_id.def_id.to_def_id();
            let body = tcx.optimized_mir(def_id);
            let mut analyzer = Analyzer {
                tcx,
                inputs,
                alloc_param_map: BTreeMap::new(),
                param_tys: vec![],
            };
            let result = analyzer.analyze_body(body);
            let location = return_location(body).unwrap();
            return result
                .into_iter()
                .filter(|(label, _)| label.location == location)
                .collect();
        }
        vec![]
    })
    .unwrap()
}

fn ret(ls: &(Label, AbsState)) -> &AbsValue {
    ls.1.local.get(0)
}

fn as_int(v: &AbsValue) -> Vec<i128> {
    assert!(v.uintv.is_bot());
    assert!(v.floatv.is_bot());
    assert!(v.boolv.is_bot());
    assert!(v.listv.is_bot());
    assert!(v.ptrv.is_bot());
    assert!(v.optionv.is_bot());
    assert!(v.fnv.is_bot());
    v.intv.gamma().unwrap().iter().cloned().collect()
}

fn as_uint(v: &AbsValue) -> Vec<u128> {
    assert!(v.intv.is_bot());
    assert!(v.floatv.is_bot());
    assert!(v.boolv.is_bot());
    assert!(v.listv.is_bot());
    assert!(v.ptrv.is_bot());
    assert!(v.optionv.is_bot());
    assert!(v.fnv.is_bot());
    v.uintv.gamma().unwrap().iter().cloned().collect()
}

fn as_float(v: &AbsValue) -> Vec<f64> {
    assert!(v.intv.is_bot());
    assert!(v.uintv.is_bot());
    assert!(v.boolv.is_bot());
    assert!(v.listv.is_bot());
    assert!(v.ptrv.is_bot());
    assert!(v.optionv.is_bot());
    assert!(v.fnv.is_bot());
    v.floatv.gamma().unwrap().iter().cloned().collect()
}

fn as_bool(v: &AbsValue) -> Vec<bool> {
    assert!(v.intv.is_bot());
    assert!(v.uintv.is_bot());
    assert!(v.floatv.is_bot());
    assert!(v.listv.is_bot());
    assert!(v.ptrv.is_bot());
    assert!(v.optionv.is_bot());
    assert!(v.fnv.is_bot());
    v.boolv.gamma()
}

fn as_fn(v: &AbsValue) -> Vec<DefId> {
    assert!(v.intv.is_bot());
    assert!(v.uintv.is_bot());
    assert!(v.floatv.is_bot());
    assert!(v.boolv.is_bot());
    assert!(v.listv.is_bot());
    assert!(v.ptrv.is_bot());
    assert!(v.optionv.is_bot());
    v.fnv.gamma().unwrap().iter().cloned().collect()
}

fn is_none(v: &AbsValue) {
    assert!(v.intv.is_bot());
    assert!(v.uintv.is_bot());
    assert!(v.floatv.is_bot());
    assert!(v.boolv.is_bot());
    assert!(v.listv.is_bot());
    assert!(v.ptrv.is_bot());
    assert!(v.optionv.is_none());
    assert!(v.fnv.is_bot());
}

fn as_some(v: &AbsValue) -> &AbsValue {
    assert!(v.intv.is_bot());
    assert!(v.uintv.is_bot());
    assert!(v.floatv.is_bot());
    assert!(v.boolv.is_bot());
    assert!(v.listv.is_bot());
    assert!(v.ptrv.is_bot());
    assert!(v.fnv.is_bot());
    if let AbsOption::Some(box v) = &v.optionv {
        &v
    } else {
        panic!("not some")
    }
}
