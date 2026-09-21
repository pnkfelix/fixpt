//! `fixpt-engine` — execution.
//!
//! Two engines over one Core IR and one runtime:
//!
//! * [`interp`] walks the AST with an explicit control stack.
//! * `vm` (M4) compiles to bytecode.
//!
//! Both are explicit-stack machines with the same calling convention, so proper
//! tail calls, unbounded recursion depth and re-entrant `call/cc` hold in both,
//! and the conformance suite can require that they agree on every case.

pub mod frame;
pub mod interp;
pub mod prepare;
pub mod resolve;

pub use interp::Interp;
pub use prepare::Prepared;
pub use resolve::{resolve, Addressing, Addr};
