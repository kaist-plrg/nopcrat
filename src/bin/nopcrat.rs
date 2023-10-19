use std::{fs::File, path::PathBuf};

use clap::Parser;
use nopcrat::*;

#[derive(Parser, Debug)]
struct Args {
    #[arg(short, long)]
    log_file: Option<PathBuf>,
    #[arg(short, long)]
    dump_analysis_result: Option<PathBuf>,
    input: PathBuf,
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

    let mut path = args.input;
    if path.is_dir() {
        path.push("c2rust-lib.rs");
    }
    assert!(path.is_file());

    let analysis_result = ai::analysis::analyze_path(&path);
    // let analysis_result = ai::analysis::analyze_code(
    //     "
    //     ",
    // );

    if let Some(dump_file) = args.dump_analysis_result {
        let dump_file = File::create(dump_file).unwrap();
        serde_json::to_writer_pretty(dump_file, &analysis_result).unwrap();
    } else {
        for (func, params) in &analysis_result {
            println!("{}", func);
            for param in params {
                println!("  {:?}", param);
            }
        }
    }
}
