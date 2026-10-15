//! Each expression's identity as the front end written in FX-26 keeps it
//! (`parser-types.fx`): where it starts and ends, and which of the
//! expressions there it is, counted in a walk of the program's trees that
//! takes each expression before what is in it (`parser-top.fx`,
//! `number-tops`). The first there is 0; one the parser made there besides
//! (a desugaring's, a loaded file's `input`, a generative type's
//! conversions) 1, 2, …. What the checkers find of an expression is kept
//! by it (`docs/research/loads-and-places.md`).
//!
//! The Rust front end tells its expressions apart by [`ExpId`]; [`Kth`]
//! says which of the expressions at its span each is, walking the same
//! trees in the same order, so that what the Rust checker finds is keyed
//! as the FX-26 compiler looks it up (`syn::rust_facts`).

use crate::ast::{Exp, ExpId, ModItem};
use crate::check::Checker;
use crate::top::Top;
use std::collections::HashMap;

/// Which of the expressions at its span each one walked is.
#[derive(Default)]
pub struct Kth {
    /// How many have been walked at each span: its file, start and end.
    seen: HashMap<(u32, u32, u32), u32>,
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

    /// Which of the expressions at its span `e` is: 0 if it was not walked.
    pub fn of(&self, e: ExpId) -> u32 {
        self.of.get(&e).copied().unwrap_or(0)
    }

    fn exp(&mut self, c: &Checker, e: ExpId) {
        let sp = c.arena.span_of(e);
        let n = self.seen.entry((sp.file.0, sp.start, sp.end)).or_insert(0);
        self.of.insert(e, *n);
        *n += 1;
        for x in within(c, e) {
            self.exp(c, x);
        }
    }
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
