//! Memory from the system, for the heap: the second crate in the workspace
//! where `unsafe` is allowed, besides `fixpt-native` (the user's decision of
//! 2026-09-26). It sits below `fixpt-heap`, so that the heap can hold its
//! memory directly, at no cost per access; `fixpt-native` sits above it.
//!
//! Address space is reserved up front and never moves, so that a Value's
//! index is from a fixed base; pages are committed by the system as they
//! are first written (`tests/reserve.rs` measures how). Every `unsafe`
//! block says what it relies on.
#![allow(unsafe_code)]

pub mod reserve;
pub mod words;

pub use words::Words;
