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
    compiler::run(path);
}
