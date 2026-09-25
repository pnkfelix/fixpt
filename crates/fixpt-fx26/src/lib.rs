//! FX-26: the tooling's own language. See `docs/fx26.md`.
//!
//! Step 1 of that plan: the kernel — KFX, the kernel of FX-87 that Jouvelot &
//! Gifford state their rules over, with the changes the design document lists
//! — and **control effects**. `(goto r)` is the effect of an expression that
//! may not return to its continuation; `(comefrom r)` of one that may keep its
//! continuation for later (PLDI '89, §3). `cwcc` carries them in its type, and
//! masking removes them under the paper's conditions (§5).
//!
//! Checking is synthesis, FX-87 style, for now: parameters carry their types
//! and polymorphism is explicit (`plambda`, `proj`). Bidirectional checking is
//! step 3.
//!
//! This crate depends on neither FX-87 nor FX-91. It borrows FX-87's
//! algorithms — regions, subtyping, masking — by reading them; each place that
//! does says where from.

pub mod ast;
pub mod check;
pub mod parse;
pub mod standard;
pub mod unparse;

pub use check::{Checker, Checked};
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
