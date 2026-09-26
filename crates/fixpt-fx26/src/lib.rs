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

/// The object layout, generated from `fixpt_heap::layout`: tags, header
/// fields and kinds, as FX-26 definitions.
pub const LAYOUT: &str = include_str!("layout.fx");

/// Hash tables, written in FX-26: prepend to a program that uses them.
pub const TABLE: &str = include_str!("table.fx");

pub mod check;
pub mod infer;
pub mod licence;
pub mod lower;
pub mod parse;
pub mod session;
pub mod syn;
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
