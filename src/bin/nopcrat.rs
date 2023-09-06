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

    assert!(compiler::check(path), "initial");
    compiler::rename_unnamed(path);
    assert!(compiler::check(path), "after renaming");
    compiler::deduplicate(path);
    assert!(compiler::check(path), "after deduplication");
}
