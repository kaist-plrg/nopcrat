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
    analysis::find_ptr_param_use(&path);
    // analysis::run_path(path);
    // analysis::run_code(
    //     "
    //     type A = _A;
    //     type B = _B;
    //     #[derive(Copy, Clone)]
    //     struct _A { x: B, y: B };
    //     #[derive(Copy, Clone)]
    //     struct _B { x: u32, y: u32 };
    //     unsafe fn f(x: *mut A) -> B {
    //         (*x).x.x = 0;
    //         let b = (*x).x;
    //         *x = A {
    //             x: B { x: 1, y: 2 },
    //             y: B { x: 3, y: 4 },
    //         };
    //         return b;
    //     }
    // ",
    // );
}
