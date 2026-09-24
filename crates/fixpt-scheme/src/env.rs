//! The compile-time environment.
//!
//! A scope chain from symbol to [`Binding`]. Hygiene is layered on top rather
//! than built in: a renamed identifier is just another symbol that can be bound
//! here, and what it means when it is *not* bound is the expander's business
//! (`Expander::resolve`). All this module adds for that is
//! [`lookup_within`](Env::lookup_within) — looking a name up in the scopes that
//! were visible where a macro was defined.

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
    BeginForSyntax,
    DefineSyntax,
    LetSyntax,
    LetrecSyntax,
    SyntaxRules,
    Else,
    Arrow,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Binding {
    Local(VarId),
    Global(GlobalId),
    Special(Special),
    /// A macro, by index into the expander's macro table.
    Macro(u32),
}

pub struct Env {
    scopes: Vec<HashMap<Sym, Binding>>,
}

impl Env {
    pub fn new() -> Env {
        Env { scopes: vec![HashMap::new()] }
    }

    /// Just the top-level scope — what a macro transformer's expression sees,
    /// since it runs before any local binding around it exists.
    pub fn top_only(&self) -> Env {
        Env { scopes: vec![self.scopes[0].clone()] }
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

    /// Look `name` up in the outermost `limit` scopes only — the ones that
    /// were in view where a macro was defined.
    pub fn lookup_within(&self, name: Sym, limit: usize) -> Option<Binding> {
        self.scopes[..limit.min(self.scopes.len())]
            .iter()
            .rev()
            .find_map(|s| s.get(&name).copied())
    }
}

impl Default for Env {
    fn default() -> Env {
        Env::new()
    }
}
