use std::path::Path;

use clap::Parser;
use nopcrat::*;

#[derive(Parser, Debug)]
struct Args {
    input: String,
}

fn main() {
    let args = Args::parse();
    let mut path = Path::new(&args.input).to_path_buf();
    if path.is_dir() {
        path.push("c2rust-lib.rs");
    }
    assert!(path.is_file());
    // analysis::find_ptr_param_use(&path);
    // analysis::run_path(path);
    ai::analysis::analyze_code(
        "
        struct S { x: *mut T, y: i32, z: *mut R }
        struct T { x: *mut S, y: i32 }
        struct R { x: *mut W }
        struct W { x: i32 }
        unsafe fn f(s: *mut S) -> i32 {
            (*(*(*s).z).x).x = 1;
            (*(*(*s).z).x).x
        }
    ",
    );
}
