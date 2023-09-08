use std::path::Path;

use clap::Parser;
use nopcrat::*;

#[derive(Parser, Debug)]
struct Args {
    input: String,
}

fn main() {
    let args = Args::parse();
    let path = Path::new(&args.input);
    analysis::run_path(path);
    // analysis::run_code(
    //     "
    //     struct A { x: u32, y: u32 };
    //     unsafe fn f(x: *mut u32) {
    //         if !x.is_null() {
    //             *x = 1;
    //         }
    //     }
    // ",
    // );
}
