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
        fn g() -> i32 {
            0
        }
        fn f() -> i32 {
            g()
        }
    ",
    );
}
