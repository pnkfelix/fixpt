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
pub mod x86_64;
pub mod codespace;
mod control;
pub mod stencil;
pub mod faults;
pub mod symbols;
pub mod cellular;
pub mod direct;

pub use codespace::CodeSpace;

/// Whether this machine can run what this crate makes: arm64 code. Where it
/// cannot, a code space cannot be made, and so neither can any machine here;
/// the encoder and disassembler work anywhere.
pub const AVAILABLE: bool = cfg!(target_arch = "aarch64");

/// Whether this machine can run the hand-encoded cellular machine and the
/// words the Rust side compiles into it (`cellular::run_word`,
/// `run_word_compiled`): on arm64, and on x86_64 (`cellular::x64`), where
/// the rest of this crate's machines are not yet.
pub const CELLULAR_AVAILABLE: bool = cfg!(any(target_arch = "aarch64", target_arch = "x86_64"));

/// What to say where [`AVAILABLE`] is false.
pub const UNAVAILABLE: &str = "this runs arm64 machine code, and this machine is not arm64";
