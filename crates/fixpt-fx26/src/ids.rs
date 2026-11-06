//! Each expression's identity as the front end written in FX-26 keeps it
//! (`parser-types.fx`, `parser-ids.fx`): its position, its number in a
//! walk of the program's trees that takes each expression before what is
//! in it, the forms in order, from 0; where it starts and ends beside, its
//! provenance. What the checkers find of an expression is kept by it
//! (`docs/research/loads-and-places.md`, "Decided: identity by
//! position").
//!
//! The Rust front end tells its expressions apart by [`ExpId`]; [`Kth`]
//! numbers them, walking the same trees in the same order, so that what
//! the Rust checker finds is keyed as the FX-26 compiler looks it up
//! (`syn::rust_facts`).

use crate::ast::{Exp, ExpId, ModItem};
use crate::check::Checker;
use crate::top::Top;
use std::collections::HashMap;

/// A reading: a digest of the session's state before it, `s`, and the
/// text read, never 0 (the Rust checker's facts are of reading 0 until the
/// FX-26 compiler gives them its trees'). Not a count, so that whoever
/// reads the same text in the same state makes the same and needs to ask
/// no one: `readings.fx`'s `reading-of`, the same function, each character
/// folded into 40 bits by a multiplier that keeps every step in a fixnum.
pub fn reading_of(s: i64, text: &str) -> i64 {
    const MASK: i64 = (1 << 40) - 1;
    let h = text.chars().fold(s & MASK, |h, c| (h * 1_000_003 + c as i64 + 1) & MASK);
    if h == 0 { 1 } else { h }
}

/// Each expression walked, its number.
#[derive(Default)]
pub struct Kth {
    /// How many have been walked.
    seen: u32,
    of: HashMap<ExpId, u32>,
}

impl Kth {
    pub fn new() -> Kth {
        Kth::default()
    }

    /// The expressions of `top`, the next of the program's forms.
    pub fn top(&mut self, c: &Checker, top: &Top) {
        match top {
            Top::Define { exp, .. } => self.exp(c, *exp),
            Top::DefineRec { bindings, .. } => bindings.iter().for_each(|(_, _, e)| self.exp(c, *e)),
            Top::Exp(k) => self.exp(c, k.exp),
            _ => {}
        }
    }

    /// Whether `e` was walked: one of the forms' given.
    pub fn walked(&self, e: ExpId) -> bool {
        self.of.contains_key(&e)
    }

    /// `e`'s number: 0 if it was not walked.
    pub fn of(&self, e: ExpId) -> u32 {
        self.of.get(&e).copied().unwrap_or(0)
    }

    fn exp(&mut self, c: &Checker, e: ExpId) {
        self.of.insert(e, self.seen);
        self.seen += 1;
        for x in within(c, e) {
            self.exp(c, x);
        }
    }
}

/// `roots` and every expression in them: what is inside one, by the trees'
/// structure, not by where it is written (a template's parts share a use's
/// span, and an argument placed twice is one span at two places;
/// `docs/research/loads-and-places.md`, "Decided: identity by position").
pub(crate) fn subtrees(c: &Checker, roots: &[ExpId]) -> std::collections::HashSet<ExpId> {
    let mut out = std::collections::HashSet::new();
    let mut stack = roots.to_vec();
    while let Some(x) = stack.pop() {
        if out.insert(x) {
            stack.extend(within(c, x));
        }
    }
    out
}

/// Each expression's parent, the one it is directly in, of every
/// expression made: what is around one, by structure (`subtrees`).
pub(crate) fn parents(c: &Checker) -> HashMap<ExpId, ExpId> {
    let mut out = HashMap::new();
    for e in c.arena.exp_ids() {
        for x in within(c, e) {
            out.insert(x, e);
        }
    }
    out
}

/// The expressions in `e`, in the order the trees are written
/// (`sexp::show_top`, and the parser's datatypes in `parser-types.fx`).
fn within(c: &Checker, e: ExpId) -> Vec<ExpId> {
    match c.arena.exp_at(e) {
        Exp::Var(_) | Exp::Int(_) | Exp::Bool(_) | Exp::Str(_) | Exp::Char(_) | Exp::Float(_) | Exp::Symbol(_) | Exp::Unit => Vec::new(),
        Exp::Lambda { body, .. } | Exp::PLambda { body, .. } | Exp::LetRegion { body, .. } | Exp::Proj { body, .. } => vec![*body],
        Exp::App { fun, args } => std::iter::once(*fun).chain(args.iter().copied()).collect(),
        Exp::RLambda { region, lambda } => vec![*region, *lambda],
        Exp::If { test, then, els } => vec![*test, *then, *els],
        Exp::Letrec { bindings, body } => bindings.iter().map(|(_, _, x)| *x).chain([*body]).collect(),
        Exp::Let { bindings, body } => bindings.iter().map(|(_, x)| *x).chain([*body]).collect(),
        Exp::Begin(items) => items.clone(),
        Exp::Prompt { tag, body, handler } => vec![*tag, *body, *handler],
        Exp::The { exp, .. } | Exp::Convention { exp, .. } => vec![*exp],
        Exp::Bloblet { args, .. } => args.clone(),
        Exp::Module(items) => items
            .iter()
            .flat_map(|item| match item {
                ModItem::Abs { up_fn, down_fn, .. } => vec![*up_fn, *down_fn],
                ModItem::Desc { .. } => Vec::new(),
                ModItem::Val { init, .. } => vec![*init],
                ModItem::Rec(group) => group.iter().map(|(_, _, x)| *x).collect(),
            })
            .collect(),
        Exp::With { body, .. } => vec![*body],
        Exp::Product(fields) => fields.iter().map(|(_, x)| *x).collect(),
        Exp::Extract(x, _) | Exp::Sum(_, x) => vec![*x],
        Exp::TagCase { scrutinee, arms, els } => {
            std::iter::once(*scrutinee).chain(arms.iter().map(|a| a.body)).chain(els.iter().map(|(_, x)| *x)).collect()
        }
    }
}
