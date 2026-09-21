//! `fixpt-core` — the intermediate representation every front end targets.
//!
//! See [`ir`] for the grammar and why it is an arena, and [`analyze`] for the
//! single pass that fills the side tables the engines depend on.

pub mod analyze;
pub mod ir;

pub use analyze::analyze;
pub use ir::{
    Builder, ConstId, GlobalId, LambdaId, LambdaInfo, Node, NodeId, Program, VarId, VarInfo,
};
