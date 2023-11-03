use std::{
    alloc::{Layout, System},
    fs::{self, File},
    path::{Path, PathBuf},
    time::Instant,
};

use clap::Parser;
use nopcrat::*;

#[derive(Parser, Debug)]
struct Args {
    #[arg(short, long)]
    dump_analysis_result: Option<PathBuf>,
    #[arg(short, long)]
    use_analysis_result: Option<PathBuf>,

    #[arg(short, long)]
    verbose: bool,
    #[arg(short, long)]
    max_loop_head_states: Option<usize>,
    #[arg(long)]
    no_widening: bool,

    #[arg(short, long)]
    transform: bool,

    #[arg(short, long)]
    print_function: Vec<String>,
    #[arg(short, long)]
    log_file: Option<PathBuf>,
    #[arg(short, long)]
    output: Option<PathBuf>,
    input: PathBuf,
}

fn main() {
    let _t = Timer::new();
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

    let conf = ai::analysis::AnalysisConfig {
        max_loop_head_states: args.max_loop_head_states.unwrap_or(usize::MAX),
        widening: !args.no_widening,
        verbose: args.verbose,
        print_functions: args.print_function.into_iter().collect(),
    };
    let analysis_result = if let Some(dump_file) = args.use_analysis_result {
        let dump_file = File::open(dump_file).unwrap();
        serde_json::from_reader(dump_file).unwrap()
    } else {
        ai::analysis::analyze_path(path, &conf)
    };
    // let analysis_result = ai::analysis::analyze_code("");

    if args.verbose {
        for (func, params) in &analysis_result {
            println!("{}", func);
            for param in params {
                println!("  {:?}", param);
            }
        }
    }
    println!("{}", analysis_result.len());
    println!(
        "{}",
        analysis_result.values().map(|v| v.len()).sum::<usize>()
    );

    if let Some(dump_file) = args.dump_analysis_result {
        let dump_file = File::create(dump_file).unwrap();
        serde_json::to_writer_pretty(dump_file, &analysis_result).unwrap();
    }

    if !args.transform {
        return;
    }

    transform::transform_path(path, &analysis_result);
}

fn clear_dir(path: &Path) {
    for entry in fs::read_dir(path).unwrap() {
        let entry_path = entry.unwrap().path();
        if entry_path.is_dir() {
            let name = entry_path.file_name().unwrap();
            if name != "target" {
                fs::remove_dir_all(entry_path).unwrap();
            }
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

struct Timer {
    start: Instant,
}

impl Timer {
    fn new() -> Self {
        Self {
            start: Instant::now(),
        }
    }
}

impl Drop for Timer {
    fn drop(&mut self) {
        println!("{:.2}s", self.start.elapsed().as_secs_f64());
    }
}

struct OomAbortAllocator;

unsafe impl std::alloc::GlobalAlloc for OomAbortAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let ptr = System.alloc(layout);
        if ptr.is_null() {
            eprintln!("Memory allocation failed");
            std::process::exit(1);
        }
        ptr
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        System.dealloc(ptr, layout);
    }
}

#[global_allocator]
static GLOBAL: OomAbortAllocator = OomAbortAllocator;
