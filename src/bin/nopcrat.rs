use std::{fs::File, path::Path};

use clap::Parser;
use nopcrat::*;

#[derive(Parser, Debug)]
struct Args {
    #[arg(short, long)]
    log_file: Option<String>,
    input: String,
}

fn main() {
    let args = Args::parse();

    if let Some(log) = args.log_file {
        let log_file = File::create(log).unwrap();
        tracing_subscriber::fmt()
            .with_max_level(tracing::Level::INFO)
            .with_ansi(false)
            .with_writer(log_file)
            .init();
    }

    let mut path = Path::new(&args.input).to_path_buf();
    if path.is_dir() {
        path.push("c2rust-lib.rs");
    }
    assert!(path.is_file());
    ai::analysis::analyze_path(&path);

    // analysis::find_ptr_param_use(&path);
    // analysis::find_mutable_globals(&path);
    // ai::analysis::analyze_code(
    //     "
    //     ",
    // );
}
