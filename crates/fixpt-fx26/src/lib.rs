//! FX-26: the tooling's own language. See `docs/fx26.md`.
//!
//! Step 1 of that plan: the kernel — KFX, the kernel of FX-87 that Jouvelot &
//! Gifford state their rules over, with the changes the design document lists
//! — and **control effects**. `(goto r)` is the effect of an expression that
//! may not return to its continuation; `(comefrom r)` of one that may keep its
//! continuation for later (PLDI '89, §3). `cwcc` carries them in its type, and
//! masking removes them under the paper's conditions (§5).
//!
//! Checking is bidirectional (`infer`): an expression is checked against a
//! type when one is expected, which supplies `lambda` parameter types and
//! solves the binders of a polymorphic operator, so that most `proj`s and
//! `plambda`s need not be written. Written out, they mean the same thing.
//!
//! This crate depends on neither FX-87 nor FX-91. It borrows FX-87's
//! algorithms — regions, subtyping, masking — by reading them; each place that
//! does says where from.

pub mod ast;

/// The eager reader, written in FX-26: see the file's own header.
pub const EAGER_READER: &str = include_str!("eager-reader.fx");

/// The parser written in FX-26, which needs the reader's types: it is
/// compiled with it, as one program ([`front_end`]).
pub const PARSER: &str = include_str!("parser.fx");

/// The parser's `load-module` (`docs/research/first-class-modules.md`, M7),
/// written in FX-26: the files a program names, as the driver read them.
pub const PARSER_LOAD: &str = include_str!("parser-load.fx");

/// The evaluator written in FX-26, which runs the parser's trees.
pub const EVALUATOR: &str = include_str!("evaluator.fx");

/// The compiler from FX-26 to cellular words, written in FX-26.
pub const COMPILER: &str = include_str!("compile.fx");

/// Its other parts, in order: lambda lifting and the standard operations;
/// expressions; inlining and programs.
pub const COMPILER_PARTS: [(&str, &str); 3] = [
    ("compile-lift.fx", include_str!("compile-lift.fx")),
    ("compile-exps.fx", include_str!("compile-exps.fx")),
    ("compile-programs.fx", include_str!("compile-programs.fx")),
];

/// The register compiler written in FX-26 (PLAN.md 13h′ (e)): register code
/// for each lambda, as its word's twin, when `c-registers` is set.
pub const REGCODE: &str = include_str!("regcode.fx");

/// Register code's other parts, in order: expressions and their helpers;
/// the expressions' compiler proper, one recursive group; and the entry.
pub const REGCODE_PARTS: [(&str, &str); 4] = [
    ("regcode-exps.fx", include_str!("regcode-exps.fx")),
    ("regcode-core.fx", include_str!("regcode-core.fx")),
    ("regcode-modules.fx", include_str!("regcode-modules.fx")),
    ("regcode-entry.fx", include_str!("regcode-entry.fx")),
];

/// The standard operations the compiler written in FX-26 runs as runtime
/// primitives, generated from the lowering's table.
pub const STANDARD_OPS: &str = include_str!("standard.fx");

/// The arm64 encoder written in FX-26, the Rust one its oracle.
pub const ARM64: &str = include_str!("arm64.fx");

/// What the compiler to machine code written in FX-26 knows of the
/// hand-encoded machine, generated from it.
pub const NATIVE_LAYOUT: &str = include_str!("native-layout.fx");

/// Words compiled to machine code, in FX-26: the hand-encoded machine's
/// `assemble_word`, over [`ARM64`].
pub const NATIVE: &str = include_str!("native.fx");

/// The checker written in FX-26, over the parser's trees, in files of its
/// parts, in order: types and effects, printing, reading descriptions,
/// resolving them, errors, modules' descriptions, subtyping, instantiation,
/// termination, the rules, modules' rules, and programs.
pub const CHECKER_FILES: [(&str, &str); 24] = [
    ("check-types.fx", include_str!("check-types.fx")),
    ("check-print.fx", include_str!("check-print.fx")),
    ("check-read.fx", include_str!("check-read.fx")),
    ("check-syntax.fx", include_str!("check-syntax.fx")),
    ("check-args.fx", include_str!("check-args.fx")),
    ("check-generative.fx", include_str!("check-generative.fx")),
    ("check-resolve.fx", include_str!("check-resolve.fx")),
    ("check-mask.fx", include_str!("check-mask.fx")),
    ("check-kinds.fx", include_str!("check-kinds.fx")),
    ("check-errors.fx", include_str!("check-errors.fx")),
    ("check-modules.fx", include_str!("check-modules.fx")),
    ("check-subtype.fx", include_str!("check-subtype.fx")),
    ("check-calls.fx", include_str!("check-calls.fx")),
    ("check-dependent.fx", include_str!("check-dependent.fx")),
    ("check-data.fx", include_str!("check-data.fx")),
    ("check-infer.fx", include_str!("check-infer.fx")),
    ("check-close.fx", include_str!("check-close.fx")),
    ("check-terminate.fx", include_str!("check-terminate.fx")),
    ("check-letrec.fx", include_str!("check-letrec.fx")),
    ("check-facts.fx", include_str!("check-facts.fx")),
    ("check-synth.fx", include_str!("check-synth.fx")),
    ("check-modorder.fx", include_str!("check-modorder.fx")),
    ("check-module-rules.fx", include_str!("check-module-rules.fx")),
    ("check-program.fx", include_str!("check-program.fx")),
];

/// The reader, the parser, the tables, the checker, the evaluator and the
/// compiler written in FX-26, with the layout they share, as one program:
/// each needs the types of the ones before.
pub fn front_end() -> String {
    FRONT_END_FILES.iter().map(|(_, t)| *t).collect::<Vec<_>>().join("\n")
}

/// The front end's files, by name, in the order [`front_end`] joins them;
/// [`bootstrap_program`] puts `bootstrap.fx` after them.
pub const FRONT_END_FILES: [(&str, &str); 43] = [
    ("eager-reader.fx", EAGER_READER),
    ("parser.fx", PARSER),
    ("parser-load.fx", PARSER_LOAD),
    ("table.fx", TABLE),
    CHECKER_FILES[0],
    CHECKER_FILES[1],
    CHECKER_FILES[2],
    CHECKER_FILES[3],
    CHECKER_FILES[4],
    CHECKER_FILES[5],
    CHECKER_FILES[6],
    CHECKER_FILES[7],
    CHECKER_FILES[8],
    CHECKER_FILES[9],
    CHECKER_FILES[10],
    CHECKER_FILES[11],
    CHECKER_FILES[12],
    CHECKER_FILES[13],
    CHECKER_FILES[14],
    CHECKER_FILES[15],
    CHECKER_FILES[16],
    CHECKER_FILES[17],
    CHECKER_FILES[18],
    CHECKER_FILES[19],
    CHECKER_FILES[20],
    CHECKER_FILES[21],
    CHECKER_FILES[22],
    CHECKER_FILES[23],
    ("evaluator.fx", EVALUATOR),
    ("layout.fx", LAYOUT),
    ("standard.fx", STANDARD_OPS),
    ("compile.fx", COMPILER),
    COMPILER_PARTS[0],
    COMPILER_PARTS[1],
    COMPILER_PARTS[2],
    ("regcode.fx", REGCODE),
    REGCODE_PARTS[0],
    REGCODE_PARTS[1],
    REGCODE_PARTS[2],
    REGCODE_PARTS[3],
    ("arm64.fx", ARM64),
    ("native-layout.fx", NATIVE_LAYOUT),
    ("native.fx", NATIVE),
];

/// Where byte `at` of [`front_end`] (or of [`bootstrap_program`]) is, as
/// `file.fx:line:col`: for an error in the front end itself, which is
/// read as one text.
pub fn front_end_location(at: usize) -> String {
    let mut start = 0;
    for (name, text) in FRONT_END_FILES.iter().copied().chain([("bootstrap.fx", BOOTSTRAP)]) {
        if at <= start + text.len() {
            let before = &text[..at - start];
            let line = before.matches('\n').count() + 1;
            let col = before.rsplit('\n').next().map_or(0, |l| l.chars().count()) + 1;
            return format!("{name}:{line}:{col}");
        }
        start += text.len() + 1;
    }
    format!("byte {at}, past the front end")
}

/// A driver for the front end, in FX-26: a text read, parsed, checked and
/// compiled by the front end. See [`bootstrap_program`].
pub const BOOTSTRAP: &str = include_str!("bootstrap.fx");

/// Where the front end's files are in the source tree this was built from.
pub const SOURCE_DIR: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/src");

/// The front end with its driver after it, as the last expression: compiled
/// to a word and run, it gives the driver.
pub fn bootstrap_program() -> String {
    format!("{}\n{BOOTSTRAP}", front_end())
}

/// The object layout, generated from `fixpt_heap::layout`: tags, header
/// fields and kinds, as FX-26 definitions.
pub const LAYOUT: &str = include_str!("layout.fx");

/// Hash tables, written in FX-26: prepend to a program that uses them.
pub const TABLE: &str = include_str!("table.fx");

pub mod check;
pub mod compare;
pub mod infer;
mod kinds;
pub mod licence;
pub mod lemma;
pub mod lower;
mod sizes;
mod modules;
mod modorder;
pub mod parse;
pub mod session;
pub mod sexp;
pub mod syn;
mod terminate;
pub mod cellular;
pub mod standard;
pub mod top;
pub mod unparse;

pub use check::{Checker, Checked};
pub use top::Top;
pub use error::{FxError, R};

pub mod error {
    use fixpt_read::Span;

    #[derive(Clone, Debug)]
    pub struct FxError {
        pub span: Span,
        pub message: String,
    }

    impl FxError {
        pub fn at(span: Span, message: impl Into<String>) -> FxError {
            FxError { span, message: message.into() }
        }
    }

    impl std::fmt::Display for FxError {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f.write_str(&self.message)
        }
    }

    pub type R<T> = Result<T, FxError>;
}
