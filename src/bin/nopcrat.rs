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
    // analysis::find_mutable_globals(&path);
    // analysis::run_path(path);
    ai::analysis::analyze_code(
        "
        fn f(mut x: Option::<fn() -> i32>) -> i32 {
            x = Some(g);
            if x.is_some() { 0 } else { 1 }
        }
        fn g() -> i32 { 0 }
    ",
    );
}
