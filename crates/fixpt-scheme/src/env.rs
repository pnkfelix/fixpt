//! The compile-time environment.
//!
//! A scope chain from symbol to [`Binding`]. Deliberately simple, because there
//! are no macros yet — but the shape is already the one a hygienic expander
//! needs (a chain of frames, with a distinguished `Special` binding class), so
//! `syntax-rules` lands in M9 as an addition rather than a rewrite.

use fixpt_core::{GlobalId, VarId};
use fixpt_read::Sym;
use std::collections::HashMap;

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Special {
    Quote,
    Quasiquote,
    Unquote,
    UnquoteSplicing,
    If,
    Lambda,
    Define,
    DefineValues,
    DefineRecordType,
    Set,
    Begin,
    Let,
    LetStar,
    Letrec,
    LetrecStar,
    LetValues,
    LetStarValues,
    Do,
    Cond,
    Case,
    And,
    Or,
    When,
    Unless,
    Delay,
    DelayForce,
    Guard,
    WithMark,
    Else,
    Arrow,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Binding {
    Local(VarId),
    Global(GlobalId),
    Special(Special),
}

pub struct Env {
    scopes: Vec<HashMap<Sym, Binding>>,
}

impl Env {
    pub fn new() -> Env {
        Env { scopes: vec![HashMap::new()] }
    }

    pub fn push(&mut self) {
        self.scopes.push(HashMap::new());
    }
    pub fn pop(&mut self) {
        self.scopes.pop();
    }
    pub fn depth(&self) -> usize {
        self.scopes.len()
    }
    /// Unwind to a known depth — used on the error path so a failed expansion
    /// cannot leave a half-built scope behind.
    pub fn truncate(&mut self, depth: usize) {
        self.scopes.truncate(depth);
    }

    pub fn bind(&mut self, name: Sym, b: Binding) {
        self.scopes.last_mut().expect("at least one scope").insert(name, b);
    }

    /// Bind in the outermost scope: how top-level `define` works.
    pub fn bind_top(&mut self, name: Sym, b: Binding) {
        self.scopes[0].insert(name, b);
    }

    pub fn lookup(&self, name: Sym) -> Option<Binding> {
        self.scopes.iter().rev().find_map(|s| s.get(&name).copied())
    }
}

impl Default for Env {
    fn default() -> Env {
        Env::new()
    }
}
