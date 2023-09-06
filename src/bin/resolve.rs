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

    assert!(resolve::check(path), "initial");
    resolve::rename_unnamed(path);
    assert!(resolve::check(path), "after renaming");
    resolve::deduplicate(path);
    assert!(resolve::check(path), "after deduplication");
}
