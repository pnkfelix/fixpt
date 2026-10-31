//! Evidence (`docs/research/eval.md`, "Evidence"): what an effect, a region
//! or a type a variable names is, as a program runs, for `stage` and a
//! session's steps to check code against.
//!
//! The checker that checked the program printed what the code is checked
//! against whole, each variable by its name, and found, for each, the local
//! holding its evidence: `(effectrep e)`, `(regionrep r)` or `(typerep t)`,
//! at run time the text of what it is of. Given here are the names, as one
//! text, and the evidence, a list; each name is replaced by its evidence in
//! the texts ([`Given::substituted`]). A region's evidence made of no other
//! is a region of its own, a fresh name ([`fresh_region`]), which the
//! staged check binds ([`regions_in`]): two regions so named are never the
//! one, which is only more cautious than the program, never less.

use crate::runtime::Runtime;
use fixpt_heap::Value;
use std::sync::atomic::{AtomicU64, Ordering};

/// The names of the variables given evidence, and their evidence, in order.
#[derive(Clone, Debug, Default)]
pub struct Given {
    pub names: Vec<String>,
    pub reps: Vec<String>,
}

impl Given {
    /// The names, `names` a text of them apart by spaces, and the evidence,
    /// `given` a product of strings (the compilers'), or a list of them (the
    /// evaluator's); none, if not those.
    pub fn of(rt: &Runtime, names: Value, given: Value) -> Given {
        let names = if rt.heap.is_a(names, fixpt_heap::ObjType::String) { rt.heap.string_to_rust(names) } else { String::new() };
        let reps = if given.is_bloblet() {
            (2..=rt.heap.bloblet_head(given).fields).map(|k| rt.heap.bloblet_slot(given, k)).collect()
        } else {
            rt.heap.list_to_vec(given).unwrap_or_default()
        };
        let reps: Vec<String> = reps.iter().filter(|v| rt.heap.is_a(**v, fixpt_heap::ObjType::String)).map(|v| rt.heap.string_to_rust(*v)).collect();
        let names: Vec<String> = names.split_whitespace().map(str::to_string).collect();
        if names.len() == reps.len() {
            Given { names, reps }
        } else {
            Given::default()
        }
    }

    /// `text` with each name it holds, a whole token, replaced by its
    /// evidence.
    pub fn substituted(&self, text: &str) -> String {
        if self.names.is_empty() {
            return text.to_string();
        }
        let mut out = String::with_capacity(text.len());
        let mut token = String::new();
        let flush = |token: &mut String, out: &mut String| {
            match self.names.iter().position(|n| n == token) {
                Some(i) => out.push_str(&self.reps[i]),
                None => out.push_str(token),
            }
            token.clear();
        };
        for c in text.chars() {
            if c == '(' || c == ')' || c.is_whitespace() {
                flush(&mut token, &mut out);
                out.push(c);
            } else {
                token.push(c);
            }
        }
        flush(&mut token, &mut out);
        out
    }
}

/// What a fresh region's name begins with.
const FRESH: &str = "%region-";

static MADE: AtomicU64 = AtomicU64::new(0);

/// A region of its own, by a name no other has.
pub fn fresh_region() -> String {
    format!("{FRESH}{}", MADE.fetch_add(1, Ordering::Relaxed))
}

/// The fresh regions `texts` name, each once, in order: what a staged check
/// binds.
pub fn regions_in(texts: &[&str]) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    for t in texts {
        for token in t.split(|c: char| c == '(' || c == ')' || c.is_whitespace()) {
            if token.starts_with(FRESH) && !out.iter().any(|o| o == token) {
                out.push(token.to_string());
            }
        }
    }
    out
}

/// What the evaluator written in FX-26 makes of a `reify-…`
/// (`%fx26-reify-text`): `text`, given the evidence `names` and `given`;
/// or, `fresh` saying `fresh`, a region of its own.
pub fn reified_text(rt: &mut Runtime, fresh: Value, text: Value, names: Value, given: Value) -> Value {
    let shown = if rt.heap.string_to_rust(fresh) == "fresh" {
        fresh_region()
    } else {
        Given::of(rt, names, given).substituted(&rt.heap.string_to_rust(text))
    };
    rt.heap.make_string(&shown)
}

/// What a `reify-…` makes (`%fx26-reify-effect` and the others): of
/// `staged`, the product the compilers make of its operand (the module's
/// type, the effect and the result type, the operand, which is the
/// evidence given it, and the names it is evidence of),
/// the text of what follows its `field` (1, the effect, or a region's; 2,
/// the type), the evidence
/// given it in place; a region's, that, or, where the module's type's
/// field says `fresh` (a region a variable names, with no evidence), a
/// fresh one.
pub fn reified(rt: &mut Runtime, staged: Value, field: usize) -> Value {
    let product = staged.is_bloblet() && rt.heap.bloblet_head(staged).fields == 6;
    let text = |rt: &Runtime, i: usize| if product { rt.heap.string_to_rust(rt.heap.bloblet_slot(staged, i + 1)) } else { String::new() };
    let shown = if text(rt, 1) == "fresh" {
        fresh_region()
    } else {
        let given = if product { Given::of(rt, rt.heap.bloblet_slot(staged, 6), rt.heap.bloblet_slot(staged, 5)) } else { Given::default() };
        given.substituted(&text(rt, field + 1))
    };
    rt.heap.make_string(&shown)
}
