//! The native core: one of the two crates in the workspace where `unsafe` is
//! allowed (`PLAN.md` §11, decision 11); the other is `fixpt-memmgmt`, below
//! the heap, which gives it its memory.
//!
//! Everything that maps executable memory, writes machine code, or jumps into
//! it is here, behind interfaces that are safe to call: a code space mapped
//! twice (read+write to build, read+execute to run, so no address is ever both),
//! and the machines that run cellular code. The encoder (`arm64`) is ordinary
//! safe code. Every `unsafe` block says what it relies on.
//!
//! arm64 on macOS first, since that is the development machine; see
//! `docs/object-model.md`, "What this machine allows".
#![allow(unsafe_code)]

pub mod arm64;
pub mod codespace;
mod control;
pub mod stencil;
pub mod faults;
pub mod cellular;
pub mod direct;

pub use codespace::CodeSpace;
