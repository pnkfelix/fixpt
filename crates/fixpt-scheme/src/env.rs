//! The compile-time environment.
//!
//! A scope chain from symbol to [`Binding`], kept by name ([`Env`]).
//! Hygiene is layered on top rather than built in: a renamed identifier is
//! just another symbol that can be bound here, and what it means when it is
//! *not* bound is the expander's business (`Expander::resolve`). All this
//! module adds for that is [`lookup_within`](Env::lookup_within) — looking a
//! name up in the scopes that were visible where a macro was defined.

use fixpt_core::{GlobalId, VarId};
use fixpt_read::Sym;
use fixpt_hash::HashMap;

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
    DefineSyntaxParameter,
    SyntaxParameterize,
    IdentifierSyntax,
    SyntaxError,
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

/// The scope chain kept by name, not by scope (shallow binding): for each
/// symbol, its bindings, innermost last, each with the scope it is in; and
/// for each scope, the symbols bound in it, to take off when it ends. So a
/// lookup is one probe however deep the code nests, where a chain of maps
/// probed each scope in turn: a global named under a hundred `let`s, a
/// hundred probes (`TODO.md` §252).
pub struct Env {
    bound: HashMap<Sym, Vec<(u32, Binding)>>,
    /// Each scope's symbols, outermost first; one at least.
    scopes: Vec<Vec<Sym>>,
}

impl Env {
    pub fn new() -> Env {
        Env { bound: HashMap::default(), scopes: vec![Vec::new()] }
    }

    /// Just the top-level scope — what a macro transformer's expression sees,
    /// since it runs before any local binding around it exists.
    pub fn top_only(&self) -> Env {
        let top = self.scopes[0].clone();
        let bound = top.iter().filter_map(|n| self.bound.get(n).and_then(|bs| bs.first()).filter(|(d, _)| *d == 0).map(|b| (*n, vec![*b]))).collect();
        Env { bound, scopes: vec![top] }
    }

    pub fn push(&mut self) {
        self.scopes.push(Vec::new());
    }
    pub fn pop(&mut self) {
        let depth = self.scopes.len() as u32 - 1;
        for name in self.scopes.pop().expect("a scope to end") {
            let bs = self.bound.get_mut(&name).expect("bound where its scope says");
            debug_assert_eq!(bs.last().map(|(d, _)| *d), Some(depth), "a scope's binding innermost as it ends");
            bs.pop();
            if bs.is_empty() {
                self.bound.remove(&name);
            }
        }
    }
    pub fn depth(&self) -> usize {
        self.scopes.len()
    }
    /// Unwind to a known depth — used on the error path so a failed expansion
    /// cannot leave a half-built scope behind.
    pub fn truncate(&mut self, depth: usize) {
        while self.scopes.len() > depth {
            self.pop();
        }
    }

    pub fn bind(&mut self, name: Sym, b: Binding) {
        let depth = self.scopes.len() as u32 - 1;
        let bs = self.bound.entry(name).or_default();
        match bs.last_mut() {
            // Bound in this scope already: rebound.
            Some((d, old)) if *d == depth => *old = b,
            _ => {
                bs.push((depth, b));
                self.scopes.last_mut().expect("at least one scope").push(name);
            }
        }
    }

    /// Bind in the outermost scope: how top-level `define` works.
    pub fn bind_top(&mut self, name: Sym, b: Binding) {
        let bs = self.bound.entry(name).or_default();
        match bs.first_mut() {
            Some((0, old)) => *old = b,
            _ => {
                bs.insert(0, (0, b));
                self.scopes[0].push(name);
            }
        }
    }

    pub fn lookup(&self, name: Sym) -> Option<Binding> {
        self.bound.get(&name).and_then(|bs| bs.last()).map(|(_, b)| *b)
    }

    /// Look `name` up in the outermost `limit` scopes only — the ones that
    /// were in view where a macro was defined.
    pub fn lookup_within(&self, name: Sym, limit: usize) -> Option<Binding> {
        self.bound.get(&name)?.iter().rev().find(|(d, _)| (*d as usize) < limit).map(|(_, b)| *b)
    }
}

impl Default for Env {
    fn default() -> Env {
        Env::new()
    }
}
