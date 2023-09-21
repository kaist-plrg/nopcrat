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
        unsafe fn f(b: bool, p: *mut [*mut i32; 2]) -> i32 {
            let q = (*p)[0];
            let r = (*p)[1];
            *q = if b { 0 } else { 1 };
            *r = if b { 0 } else { 2 };
            *(*p)[0] + *(*p)[1]
        }
    ",
    );
}
