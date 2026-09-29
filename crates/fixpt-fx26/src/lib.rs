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

/// The evaluator written in FX-26, which runs the parser's trees.
pub const EVALUATOR: &str = include_str!("evaluator.fx");

/// The compiler from FX-26 to cellular words, written in FX-26.
pub const COMPILER: &str = include_str!("compile.fx");

/// The register compiler written in FX-26 (PLAN.md 13h′ (e)): register code
/// for each lambda, as its word's twin, when `c-registers` is set.
pub const REGCODE: &str = include_str!("regcode.fx");

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
/// resolving them, subtyping, instantiation, termination, the rules, and
/// programs.
pub const CHECKER_FILES: [(&str, &str); 9] = [
    ("check-types.fx", include_str!("check-types.fx")),
    ("check-print.fx", include_str!("check-print.fx")),
    ("check-syntax.fx", include_str!("check-syntax.fx")),
    ("check-resolve.fx", include_str!("check-resolve.fx")),
    ("check-subtype.fx", include_str!("check-subtype.fx")),
    ("check-infer.fx", include_str!("check-infer.fx")),
    ("check-terminate.fx", include_str!("check-terminate.fx")),
    ("check-synth.fx", include_str!("check-synth.fx")),
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
pub const FRONT_END_FILES: [(&str, &str); 20] = [
    ("eager-reader.fx", EAGER_READER),
    ("parser.fx", PARSER),
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
    ("evaluator.fx", EVALUATOR),
    ("layout.fx", LAYOUT),
    ("standard.fx", STANDARD_OPS),
    ("compile.fx", COMPILER),
    ("regcode.fx", REGCODE),
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
pub mod licence;
pub mod lemma;
pub mod lower;
mod sizes;
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
