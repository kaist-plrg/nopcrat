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
        unsafe fn f() -> i32 {
            let mut x: i32 = 0;
            let mut p: *mut i32 = &mut x;
            let mut q: *mut *mut i32 = &mut p;
            **q = 1;
            return **q;
        }
    ",
    );
}
