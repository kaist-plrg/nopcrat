use rustc_hir::def_id::DefId;

use super::{analysis, domains::*};
use crate::*;

mod arrays;
mod bools;
mod calls;
mod cast;
mod float;
mod fnptr;
mod int;
mod labels;
mod ptr;
mod structs;
mod uint;

fn analyze(code: &str) -> Vec<AbsState> {
    let input = compile_util::str_to_input(code);
    let config = compile_util::make_config(input);
    compile_util::run_compiler(config, |_, tcx| {
        analysis::analyze(tcx)
            .into_iter()
            .find(|(def_id, _)| {
                tcx.def_path(*def_id)
                    .to_string_no_crate_verbose()
                    .ends_with("::f")
            })
            .unwrap()
            .1
             .0
            .return_states
    })
    .unwrap()
}

fn ret(st: &AbsState) -> &AbsValue {
    st.local.get(0)
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
