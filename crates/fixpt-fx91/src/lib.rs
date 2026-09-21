//! `fixpt-fx91` — the FX-91 front end.
//!
//! FX-91 is MIT PSRG's 1991 effect-typed language: Hindley-Milner-style type
//! *and effect* inference, first-class modules with abstract types, and effect
//! polymorphism. Like the original, this is a front end onto Scheme — it
//! checks, then lowers to the Core IR the Scheme engine already runs.
//!
//! The module structure deliberately mirrors the original's file decomposition
//! (`abstract.scm`, `token.scm`, `sugar.scm`, …), because conformance failures
//! then localise to the same place the reference would put them.

pub mod ast;
pub mod check;
pub mod constraints;
pub mod env;
pub mod evaluate;
pub mod kind;
pub mod unify;
pub mod error;
pub mod free;
pub mod matching;
pub mod modules;
pub mod parse;
pub mod subtype;
pub mod sugar;
pub mod syms;
pub mod typecheck;
pub mod unparse;

pub use ast::{Arena, Fx, FxId, Kind};
pub use error::{ErrorKind, FxError};
pub use parse::Parser;
