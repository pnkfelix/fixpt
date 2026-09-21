//! FX-87 — MIT PSRG's 1987 effect-typed language, as a front end onto the
//! `fixpt` Scheme engine.
//!
//! The architecture is the original's. `type-and-eval` in the reference checks
//! a form with `desc-of-exp` and then runs `(fx-eval (erase-type node))` — it
//! type- and effect-checks, erases the types away, and hands plain Scheme to an
//! evaluator. This crate does the same, onto the Core IR, which is why it
//! inherits both engines, heap images and single-binary builds without any of
//! that being written twice.
//!
//! # How it differs from [`fixpt_fx91`]
//!
//! They are separate languages, four years apart, and the difference is not
//! cosmetic:
//!
//! * **Checking, not inference.** FX-87 asks you to write the types down and
//!   checks them. There is no unification, no union-find and no value
//!   restriction — and no way to omit an annotation.
//! * **Subtyping and subeffecting.** Which is what replaces inference: a
//!   `pure` subroutine is usable where an effectful one was wanted, and a
//!   smaller region where a larger one was. `inequal.lisp` is a whole file with
//!   no counterpart in 1991.
//! * **Regions are a kind.** Effects are `(read r)`, `(write r)`, `(alloc r)`
//!   over regions, and `poly` abstracts over regions as readily as over types.
//! * **Effect masking.** An allocation whose region cannot escape can be
//!   dropped from the effect, which is how `(let ((x (new 3))) …)` comes out
//!   `pure`.
//!
//! Conformance is checked against the same corpus the reference produced; see
//! `tests/conformance/fx87/`.

pub mod ast;
pub mod error;
pub mod parse;
pub mod syms;
pub mod unparse;

pub use ast::{Arena, Desc, DescId, Exp, ExpId, Kind};
pub use error::{FxError, R};
pub use parse::{DScope, Parser};
