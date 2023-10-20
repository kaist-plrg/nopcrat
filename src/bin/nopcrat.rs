use std::{
    fs::{self, File},
    path::{Path, PathBuf},
};

use clap::Parser;
use nopcrat::*;

#[derive(Parser, Debug)]
struct Args {
    #[arg(short, long)]
    log_file: Option<PathBuf>,
    #[arg(short, long)]
    dump_analysis_result: Option<PathBuf>,
    #[arg(long)]
    load_analysis_result: Option<PathBuf>,
    #[arg(short, long)]
    output: Option<PathBuf>,
    #[arg(short, long)]
    analysis_only: bool,
    input: PathBuf,
}

fn main() {
    let mut args = Args::parse();

    if let Some(log) = args.log_file {
        let log_file = File::create(log).unwrap();
        tracing_subscriber::fmt()
            .with_max_level(tracing::Level::INFO)
            .with_ansi(false)
            .with_writer(log_file)
            .init();
    }

    let path = if let Some(output) = &mut args.output {
        output.push(args.input.file_name().unwrap());
        if output.exists() {
            assert!(output.is_dir());
            clear_dir(output);
        } else {
            fs::create_dir(&output).unwrap();
        }
        copy_dir(&args.input, output, true);
        output
    } else {
        &mut args.input
    };
    if path.is_dir() {
        path.push("c2rust-lib.rs");
    }
    assert!(path.is_file());

    let analysis_result = if let Some(dump_file) = args.load_analysis_result {
        let dump_file = File::open(dump_file).unwrap();
        serde_json::from_reader(dump_file).unwrap()
    } else {
        ai::analysis::analyze_path(path)
    };
    // let analysis_result = ai::analysis::analyze_code("");

    for (func, params) in &analysis_result {
        println!("{}", func);
        for param in params {
            println!("  {:?}", param);
        }
    }
    if let Some(dump_file) = args.dump_analysis_result {
        let dump_file = File::create(dump_file).unwrap();
        serde_json::to_writer_pretty(dump_file, &analysis_result).unwrap();
    }

    if args.analysis_only {
        return;
    }

    transform::transform_path(path, &analysis_result);
}

fn clear_dir(path: &Path) {
    for entry in fs::read_dir(path).unwrap() {
        let entry_path = entry.unwrap().path();
        if entry_path.is_dir() {
            fs::remove_dir_all(entry_path).unwrap();
        } else {
            fs::remove_file(entry_path).unwrap();
        }
    }
}

fn copy_dir(src: &Path, dst: &Path, root: bool) {
    for entry in fs::read_dir(src).unwrap() {
        let src_path = entry.unwrap().path();
        let name = src_path.file_name().unwrap();
        let dst_path = dst.join(name);
        if src_path.is_file() {
            fs::copy(src_path, dst_path).unwrap();
        } else if src_path.is_dir() && (!root || name != "target") {
            fs::create_dir(&dst_path).unwrap();
            copy_dir(&src_path, &dst_path, false);
        }
    }
}
