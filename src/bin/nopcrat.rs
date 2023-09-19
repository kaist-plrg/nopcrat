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
        "fn f() -> u128 {
            let a = 3;
            let a = a + 4;
            let a = a - 1;
            let a = a * 3;
            let a = a / 2;
            let a = a % 5;
            let a = a << 3;
            let a = a >> 1;
            let a = a & 63;
            let a = a | 0;
            let a = a ^ 1;
            let a = !a;
            a
        }
    ",
    );
}
