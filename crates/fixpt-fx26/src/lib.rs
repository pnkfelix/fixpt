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

/// The compiler from FX-26 to threaded words, written in FX-26.
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

/// The checker written in FX-26, over the parser's trees.
pub const CHECKER: &str = include_str!("check.fx");

/// The reader, the parser, the tables, the checker, the evaluator and the
/// compiler written in FX-26, with the layout they share, as one program:
/// each needs the types of the ones before.
pub fn front_end() -> String {
    format!("{EAGER_READER}\n{PARSER}\n{TABLE}\n{CHECKER}\n{EVALUATOR}\n{LAYOUT}\n{STANDARD_OPS}\n{COMPILER}\n{REGCODE}\n{ARM64}\n{NATIVE_LAYOUT}\n{NATIVE}")
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
pub mod threaded;
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
