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

/// The names of the variables given evidence, and their evidence, in order:
/// its text, and its rep, where it has one (`heap-types.md`, step 3; a
/// rep `fixpt_reps::fill` takes).
#[derive(Clone, Debug, Default)]
pub struct Given {
    pub names: Vec<String>,
    pub reps: Vec<String>,
    pub as_reps: Vec<Option<fixpt_reps::Rep>>,
}

impl Given {
    /// The names, `names` a text of them apart by spaces, and the evidence,
    /// `given` a product of pieces of it (the compilers'), or a list of them
    /// (the evaluator's), each its text or the product of its text and its
    /// rep ([`evidence`]); none, if not those.
    pub fn of(rt: &Runtime, names: Value, given: Value) -> Given {
        let names = if rt.heap.is_a(names, fixpt_heap::ObjType::String) { rt.heap.string_to_rust(names) } else { String::new() };
        let pieces = if given.is_bloblet() {
            rt.heap.bloblet_values(given)
        } else {
            rt.heap.list_to_vec(given).unwrap_or_default()
        };
        let string = |v: Value| rt.heap.is_a(v, fixpt_heap::ObjType::String);
        let (mut reps, mut as_reps) = (Vec::new(), Vec::new());
        for v in pieces {
            if string(v) {
                reps.push(rt.heap.string_to_rust(v));
                as_reps.push(None);
            } else if rt.heap.is_product(v) && rt.heap.bloblet_len(v) == 2 && string(rt.heap.product_field(v, 1)) {
                reps.push(rt.heap.string_to_rust(rt.heap.product_field(v, 1)));
                as_reps.push(fixpt_reps::heap::from_heap(&rt.heap, rt.heap.product_field(v, 2), true).ok());
            }
        }
        let names: Vec<String> = names.split_whitespace().map(str::to_string).collect();
        if names.len() == reps.len() {
            Given { names, reps, as_reps }
        } else {
            Given::default()
        }
    }

    /// `rep` with each hole the evidence's variables name filled with its
    /// rep (`fixpt_reps::fill`); none where a hole is left, or a piece of
    /// evidence it names has no rep.
    pub fn filled(&self, rep: &fixpt_reps::Rep) -> Option<fixpt_reps::Rep> {
        let mut given = Vec::new();
        for (n, r) in self.names.iter().zip(&self.as_reps) {
            if rep.holes.contains(n) {
                given.push((n.as_str(), r.as_ref()?));
            }
        }
        // A type variable's occurrence is a `var` node (`fixpt-fx26`'s `reps.rs`).
        let filled = fixpt_reps::fill::fill(rep, &given, "var").ok()?;
        filled.holes.is_empty().then_some(filled)
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
/// And its rep too, where the checker noted one and the evidence given has
/// them: [`evidence`].
pub fn reified(rt: &mut Runtime, staged: Value, field: usize) -> Value {
    let product = rt.heap.is_product(staged) && rt.heap.bloblet_len(staged) == 6;
    let text = |rt: &Runtime, i: usize| if product { rt.heap.string_to_rust(rt.heap.product_field(staged, i)) } else { String::new() };
    if text(rt, 1) == "fresh" {
        return rt.heap.make_string(&fresh_region());
    }
    let given = if product { Given::of(rt, rt.heap.product_field(staged, 5), rt.heap.product_field(staged, 4)) } else { Given::default() };
    let shown = given.substituted(&text(rt, field + 1));
    let rep = if product { fixpt_reps::heap::from_heap(&rt.heap, rt.heap.product_field(staged, 6), true).ok() } else { None };
    let rep = rep.and_then(|r| if r.holes.is_empty() { Some(r) } else { given.filled(&r) });
    evidence(rt, &shown, rep.as_ref())
}

/// A piece of evidence, as the program holds it: its text, and its rep if
/// it has one, a product of the two (`#f` for none).
pub fn evidence(rt: &mut Runtime, text: &str, rep: Option<&fixpt_reps::Rep>) -> Value {
    let base = rt.heap.push_root(Value::FALSE);
    if let Some(r) = rep {
        let v = fixpt_reps::heap::to_heap(&mut rt.heap, r);
        rt.heap.set_root_at(base, v);
    }
    let text = rt.heap.make_string(text);
    rt.heap.push_root(text);
    let (rep, text) = (rt.heap.root_at(base), rt.heap.root_at(base + 1));
    let v = rt.heap.make_frozen(fixpt_heap::layout::kind("product"), &[text, rep]);
    rt.heap.pop_roots_to(base);
    v
}
