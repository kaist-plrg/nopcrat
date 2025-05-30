use std::{
    collections::BTreeMap,
    fs,
    path::{Path, PathBuf},
    process::Command,
    sync::{Arc, Mutex},
};

use etrace::ok_or;
use rustc_errors::{
    emitter::Emitter, registry::Registry, translation::Translate, FluentBundle, Level,
};
use rustc_feature::UnstableFeatures;
use rustc_hash::FxHashMap;
use rustc_interface::{create_and_enter_global_ctxt, passes::parse, Config};
use rustc_middle::ty::TyCtxt;
use rustc_session::{
    config::{CrateType, ErrorOutputType, Input, Options},
    EarlyDiagCtxt,
};
use rustc_span::{
    edition::Edition, fatal_error::FatalError, source_map::SourceMap, BytePos, FileName,
    RealFileName, Span, SpanData, SyntaxContext,
};
use rustfix::{LinePosition, LineRange, Replacement, Snippet, Solution, Suggestion};
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct LoHi {
    lo: u32,
    hi: u32,
}

impl LoHi {
    #[inline]
    fn new(lo: u32, hi: u32) -> Self {
        Self { lo, hi }
    }

    #[inline]
    pub fn from_span(span: Span) -> Self {
        assert!(span.ctxt().is_root());
        assert!(span.parent().is_none());
        Self::new(span.lo().0, span.hi().0)
    }

    #[inline]
    pub fn from_span_data(span: SpanData) -> Self {
        assert!(span.ctxt.is_root());
        assert!(span.parent.is_none());
        Self::new(span.lo.0, span.hi.0)
    }

    #[inline]
    pub fn to_span(self) -> Span {
        Span::new(
            BytePos(self.lo),
            BytePos(self.hi),
            SyntaxContext::root(),
            None,
        )
    }

    #[inline]
    pub fn to_span_data(self) -> SpanData {
        SpanData {
            lo: BytePos(self.lo),
            hi: BytePos(self.hi),
            ctxt: SyntaxContext::root(),
            parent: None,
        }
    }
}

pub fn run_compiler<R: Send, F: FnOnce(TyCtxt<'_>) -> R + Send>(
    config: Config,
    f: F,
) -> Result<R, FatalError> {
    rustc_driver::catch_fatal_errors(|| {
        rustc_interface::run_compiler(config, |compiler| {
            let krate = parse(&compiler.sess);
            create_and_enter_global_ctxt(compiler, krate, f)
        })
    })
}

pub fn make_config(input: Input) -> Config {
    let opts = find_deps();
    Config {
        opts: Options {
            maybe_sysroot: Some(PathBuf::from(sys_root())),
            search_paths: opts.search_paths,
            externs: opts.externs,
            unstable_features: UnstableFeatures::Allow,
            crate_types: vec![CrateType::Rlib],
            debug_assertions: false,
            edition: Edition::Edition2021,
            ..Options::default()
        },
        crate_cfg: Vec::new(),
        crate_check_cfg: Vec::new(),
        input,
        output_dir: None,
        output_file: None,
        ice_file: None, // Note: rustc_driver:ice_path() is not public anymore
        file_loader: None,
        locale_resources: rustc_driver::DEFAULT_LOCALE_RESOURCES.to_owned(),
        lint_caps: FxHashMap::default(),
        psess_created: Some(Box::new(|ps| {
            ps.dcx().make_silent(None, false);
        })),
        register_lints: None,
        override_queries: None,
        make_codegen_backend: None,
        registry: Registry::new(rustc_errors::codes::DIAGNOSTICS),
        hash_untracked_state: None,
        using_internal_features: &rustc_driver::USING_INTERNAL_FEATURES,
        expanded_args: Vec::new(),
    }
}

pub fn make_counting_config(input: Input) -> (Config, Arc<Mutex<usize>>) {
    let mut config = make_config(input);
    let arc = Arc::new(Mutex::new(0));
    let emitter = CountingEmitter(arc.clone());
    config.psess_created = Some(Box::new(|ps| {
        ps.dcx().set_emitter(Box::new(emitter));
    }));
    (config, arc)
}

pub fn str_to_input(code: &str) -> Input {
    Input::Str {
        name: FileName::Custom("main.rs".to_string()),
        input: code.to_string(),
    }
}

pub fn path_to_input(path: &Path) -> Input {
    Input::File(path.to_path_buf())
}

pub fn span_to_path(span: Span, source_map: &SourceMap) -> Option<PathBuf> {
    if let FileName::Real(RealFileName::LocalPath(p)) = source_map.span_to_filename(span) {
        Some(p)
    } else {
        None
    }
}

pub fn apply_suggestions<P: AsRef<Path>>(suggestions: &BTreeMap<P, Vec<Suggestion>>) {
    for (path, suggestions) in suggestions {
        let code = String::from_utf8(fs::read(path).unwrap()).unwrap();
        // for suggestion in suggestions {
        // println!("{:?}", path.as_ref());
        // println!("{:?}", suggestion.snippets[0].line_range);
        // println!("{:?}", suggestion.snippets[0].range);
        // println!("{}", suggestion.solutions[0].replacements[0].replacement);
        // println!();
        // }
        let fixed = rustfix::apply_suggestions(&code, suggestions).unwrap();
        fs::write(path, fixed.as_bytes()).unwrap();
    }
}

pub fn make_suggestion(snippet: Snippet, replacement: String) -> Suggestion {
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
        file_name: fname.prefer_remapped_unconditionaly().to_string(),
        line_range,
        range: (lo_offset as usize)..(hi_offset as usize),
        text: (
            "".into(),
            source_map.span_to_snippet(span).unwrap(),
            "".into(),
        ),
    }
}

struct CountingEmitter(Arc<Mutex<usize>>);

impl Translate for CountingEmitter {
    fn fluent_bundle(&self) -> Option<&FluentBundle> {
        None
    }

    fn fallback_fluent_bundle(&self) -> &FluentBundle {
        panic!()
    }
}

impl Emitter for CountingEmitter {
    fn emit_diagnostic(&mut self, diag: rustc_errors::DiagInner, _: &Registry) {
        if matches!(diag.level(), Level::Error) {
            *self.0.lock().unwrap() += 1;
        }
    }

    fn source_map(&self) -> Option<&SourceMap> {
        None
    }
}

fn find_deps() -> Options {
    let mut args = vec!["a.rs".to_string()];

    let dir = std::env::var("DIR").unwrap_or_else(|_| ".".to_string());
    let dep = format!("{}/deps_crate/target/debug/deps", dir);
    if let Ok(dir) = fs::read_dir(&dep) {
        args.push("-L".to_string());
        args.push(format!("dependency={}", dep));

        for f in dir {
            let f = ok_or!(f, continue);
            let f = f.file_name().to_str().unwrap().to_string();
            if !f.ends_with(".rlib") {
                continue;
            }
            let i = f.find('-').unwrap();
            let name = f[3..i].to_string();
            let d = format!("{}={}/{}", name, dep, f);
            args.push("--extern".to_string());
            args.push(d);
        }
    }

    let mut handler = EarlyDiagCtxt::new(ErrorOutputType::default());
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
