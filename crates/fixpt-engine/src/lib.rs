//! `fixpt-engine` — execution.
//!
//! Two engines over one Core IR and one runtime:
//!
//! * [`interp`] walks the heap-resident Core IR with an explicit control stack.
//! * `vm` (M4) compiles it to bytecode.
//!
//! Both execute code that lives *in the heap*, so a dumped image can be resumed
//! by either — nothing they run is held in Rust.
//!
//! Both are explicit-stack machines with the same calling convention, so proper
//! tail calls, unbounded recursion depth and re-entrant `call/cc` hold in both,
//! and the conformance suite can require that they agree on every case.

pub mod frame;
pub mod interp;
pub mod prepare;

pub use interp::Interp;
pub use prepare::Prepared;
