use std::{
    collections::BTreeMap,
    path::{Path, PathBuf},
    process::Command,
};

use rustc_data_structures::sync::Lrc;
use rustc_errors::{
    emitter::Emitter, registry::Registry, translation::Translate, FluentBundle, Handler,
};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_interface::{interface::Compiler, Config};
use rustc_session::{
    config::{CheckCfg, ErrorOutputType, Input, Options},
    EarlyErrorHandler,
};
use rustc_span::{
    source_map::{FileName, SourceMap},
    RealFileName, Span,
};
use rustfix::{LinePosition, LineRange, Replacement, Snippet, Solution, Suggestion};

pub fn run_compiler<R: Send, F: FnOnce(&Compiler) -> R + Send>(config: Config, f: F) -> Option<R> {
    rustc_driver::catch_fatal_errors(|| rustc_interface::run_compiler(config, f)).ok()
}

pub fn make_config(input: Input) -> Config {
    let opts = find_deps();
    Config {
        opts: Options {
            maybe_sysroot: Some(PathBuf::from(sys_root())),
            search_paths: opts.search_paths,
            externs: opts.externs,
            ..Options::default()
        },
        crate_cfg: FxHashSet::default(),
        crate_check_cfg: CheckCfg::default(),
        input,
        output_dir: None,
        output_file: None,
        ice_file: rustc_driver::ice_path().clone(),
        file_loader: None,
        locale_resources: rustc_driver_impl::DEFAULT_LOCALE_RESOURCES,
        lint_caps: FxHashMap::default(),
        parse_sess_created: Some(Box::new(|ps| {
            ps.span_diagnostic = Handler::with_emitter(Box::new(SilentEmitter));
        })),
        register_lints: None,
        override_queries: None,
        make_codegen_backend: None,
        registry: Registry::new(rustc_error_codes::DIAGNOSTICS),
    }
}

pub fn str_to_input(code: &str) -> Input {
    Input::Str {
        name: FileName::Custom("main.rs".to_string()),
        input: code.to_string(),
    }
}

pub fn path_to_input(path: &Path) -> Input {
    Input::File(PathBuf::from(path))
}

pub fn span_to_path(span: Span, source_map: &SourceMap) -> Option<PathBuf> {
    if let FileName::Real(RealFileName::LocalPath(p)) = source_map.span_to_filename(span) {
        Some(p)
    } else {
        None
    }
}

pub fn make_suggestion(snippet: Snippet, replacement: &str) -> Suggestion {
    let replacement = Replacement {
        snippet: snippet.clone(),
        replacement: replacement.to_string(),
    };
    let solution = Solution {
        message: "".into(),
        replacements: vec![replacement],
    };
    Suggestion {
        message: "".into(),
        snippets: vec![snippet],
        solutions: vec![solution],
    }
}

pub fn span_to_snippet(span: Span, source_map: &SourceMap) -> Snippet {
    let fname = source_map.span_to_filename(span);
    let file = source_map.get_source_file(&fname).unwrap();
    let lo = file.lookup_file_pos_with_col_display(span.lo());
    let hi = file.lookup_file_pos_with_col_display(span.hi());
    let line_range = LineRange {
        start: LinePosition {
            line: lo.0,
            column: lo.2,
        },
        end: LinePosition {
            line: hi.0,
            column: hi.2,
        },
    };
    let lo_offset = file.original_relative_byte_pos(span.lo()).0;
    let hi_offset = file.original_relative_byte_pos(span.hi()).0;
    Snippet {
        file_name: fname.prefer_remapped().to_string(),
        line_range,
        range: (lo_offset as usize)..(hi_offset as usize),
        text: (
            "".into(),
            source_map.span_to_snippet(span).unwrap(),
            "".into(),
        ),
    }
}

struct SilentEmitter;

impl Translate for SilentEmitter {
    fn fluent_bundle(&self) -> Option<&Lrc<FluentBundle>> {
        None
    }

    fn fallback_fluent_bundle(&self) -> &FluentBundle {
        panic!()
    }
}

impl Emitter for SilentEmitter {
    fn emit_diagnostic(&mut self, _: &rustc_errors::Diagnostic) {}

    fn source_map(&self) -> Option<&Lrc<SourceMap>> {
        None
    }
}

const DEPS: [&str; 0] = [];

fn find_deps() -> Options {
    let mut args = vec!["a.rs".to_string()];

    if !DEPS.is_empty() {
        let dep = "deps_crate/target/debug/deps";
        args.push("-L".to_string());
        args.push(format!("dependency={}", dep));

        let files: BTreeMap<_, _> = std::fs::read_dir(dep)
            .unwrap()
            .filter_map(|f| {
                let f = f.ok()?;
                let f = f.file_name().to_str().unwrap().to_string();
                if !f.ends_with(".rlib") {
                    return None;
                }
                let i = f.find('-')?;
                Some((f[3..i].to_string(), f))
            })
            .collect();
        for d in &DEPS {
            let d = format!("{}={}/{}", d, dep, files.get(&d.to_string()).unwrap());
            args.push("--extern".to_string());
            args.push(d);
        }
    }

    let mut handler = EarlyErrorHandler::new(ErrorOutputType::default());
    let matches = rustc_driver::handle_options(&handler, &args).unwrap();
    rustc_session::config::build_session_options(&mut handler, &matches)
}

fn sys_root() -> String {
    std::env::var("SYSROOT")
        .ok()
        .map(PathBuf::from)
        .or_else(|| {
            let home = std::env::var("RUSTUP_HOME")
                .or_else(|_| std::env::var("MULTIRUST_HOME"))
                .ok();
            let toolchain = std::env::var("RUSTUP_TOOLCHAIN")
                .or_else(|_| std::env::var("MULTIRUST_TOOLCHAIN"))
                .ok();
            toolchain_path(home, toolchain)
        })
        .or_else(|| {
            Command::new("rustc")
                .arg("--print")
                .arg("sysroot")
                .output()
                .ok()
                .and_then(|out| String::from_utf8(out.stdout).ok())
                .map(|s| PathBuf::from(s.trim()))
        })
        .or_else(|| option_env!("SYSROOT").map(PathBuf::from))
        .or_else(|| {
            let home = option_env!("RUSTUP_HOME")
                .or(option_env!("MULTIRUST_HOME"))
                .map(ToString::to_string);
            let toolchain = option_env!("RUSTUP_TOOLCHAIN")
                .or(option_env!("MULTIRUST_TOOLCHAIN"))
                .map(ToString::to_string);
            toolchain_path(home, toolchain)
        })
        .map(|pb| pb.to_string_lossy().to_string())
        .unwrap()
}

fn toolchain_path(home: Option<String>, toolchain: Option<String>) -> Option<PathBuf> {
    home.and_then(|home| {
        toolchain.map(|toolchain| {
            let mut path = PathBuf::from(home);
            path.push("toolchains");
            path.push(toolchain);
            path
        })
    })
}
