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
    // ai::analysis::analyze_path(&path);
    // analysis::find_ptr_param_use(&path);
    // analysis::find_mutable_globals(&path);
    ai::analysis::analyze_code(
        "
        unsafe fn f(b: bool) -> i32 {
            let mut x1 = 0;
            let mut p1: *mut i32 = &mut x1;
            let mut q1: *mut *mut i32 = &mut p1;
            g(q1);
            *p1
        }
        unsafe fn g(p: *mut *mut i32) {
            let mut x = 0;
            *p = &mut x;
        }
    ",
    );
}
