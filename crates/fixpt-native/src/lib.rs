//! The native core: the one crate in the workspace where `unsafe` is allowed
//! (`PLAN.md` §11, decision 11).
//!
//! Everything that maps executable memory, writes machine code, or jumps into
//! it is here, behind interfaces that are safe to call: a code space mapped
//! twice (read+write to build, read+execute to run, so no address is ever both),
//! and the machines that run threaded code. The encoder (`arm64`) is ordinary
//! safe code. Every `unsafe` block says what it relies on.
//!
//! arm64 on macOS first, since that is the development machine; see
//! `docs/object-model.md`, "What this machine allows".
#![allow(unsafe_code)]

pub mod arm64;
pub mod codespace;
pub mod threaded;

pub use codespace::CodeSpace;
