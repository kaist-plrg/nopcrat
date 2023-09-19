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
        struct A { x: u32, y: u32 }
        struct B { x: A, y: A }
        fn f(a: bool) -> u32 {
            let b = [A { x: 1, y: 2 }, A { x: 3, y: 4 }];
            let x = if a { 0 } else { 1 };
            b[x].y = 5;
            b[0].y
        }
    ",
    );
}
