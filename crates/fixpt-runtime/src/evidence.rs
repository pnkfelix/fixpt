//! Evidence (`docs/research/eval.md`, "Evidence"): what an effect, a region
//! or a type a variable names is, as a program runs, for `stage` and a
//! session's steps to check code against.
//!
//! The checker that checked the program noted what the code is checked as,
//! as a rep whose holes are the variables it names, and found, for each,
//! the local holding its evidence: `(effectrep e)`, `(regionrep r)` or
//! `(typerep t)`, at run time a rep of what it is of, its root an
//! `evidence` node (`fixpt_reps::fill`; `docs/research/heap-types.md`,
//! steps 3 and 6). Given here are the names, as one text, and the
//! evidence; the holes are filled by it ([`Given::filled`]). A region's
//! evidence made of no other is a region of its own: a region constant by
//! a name no other has ([`fresh_region`]), opaque and distinct from every
//! other, which is only more cautious than the program, never less.

use crate::runtime::Runtime;
use fixpt_heap::Value;
use std::sync::atomic::{AtomicU64, Ordering};

/// The names of the variables given evidence, and their evidence, in order,
/// each its rep, where it has one.
#[derive(Clone, Debug, Default)]
pub struct Given {
    pub names: Vec<String>,
    pub reps: Vec<Option<fixpt_reps::Rep>>,
}

impl Given {
    /// The names, `names` a text of them apart by spaces, and the evidence,
    /// `given` a product of pieces of it (the compilers'), each a rep in the
    /// heap (`#f` for none); none, if not that.
    pub fn of(rt: &Runtime, names: Value, given: Value) -> Given {
        let pieces = if given.is_bloblet() { rt.heap.bloblet_values(given) } else { Vec::new() };
        let reps = pieces.iter().map(|v| fixpt_reps::heap::from_heap(&rt.heap, *v, true).ok()).collect();
        Given::named(rt, names, reps)
    }

    /// The same, `reps` a list of the pieces' reps' binary forms, each empty
    /// for none (the evaluator's, `ev-given-reps`).
    pub fn of_bytes(rt: &Runtime, names: Value, reps: Value) -> Given {
        let reps = rt.heap.list_to_vec(reps).unwrap_or_default();
        let reps = reps.iter().map(|b| bytes_of(rt, *b).and_then(|b| fixpt_reps::binary::decode(&b, fixpt_reps::heap::validate_all()).ok())).collect();
        Given::named(rt, names, reps)
    }

    fn named(rt: &Runtime, names: Value, reps: Vec<Option<fixpt_reps::Rep>>) -> Given {
        let names = if rt.heap.is_a(names, fixpt_heap::ObjType::String) { rt.heap.string_to_rust(names) } else { String::new() };
        let names: Vec<String> = names.split_whitespace().map(str::to_string).collect();
        if names.len() == reps.len() {
            Given { names, reps }
        } else {
            Given::default()
        }
    }

    /// `rep` with each hole the evidence's variables name filled with its
    /// rep (`fixpt_reps::fill`); none where a hole is left, or a piece of
    /// evidence it names has no rep.
    pub fn filled(&self, rep: &fixpt_reps::Rep) -> Option<fixpt_reps::Rep> {
        if rep.holes.is_empty() {
            return Some(rep.clone());
        }
        let mut given = Vec::new();
        for (n, r) in self.names.iter().zip(&self.reps) {
            if rep.holes.contains(n) {
                given.push((n.as_str(), r.as_ref()?));
            }
        }
        // A type variable's occurrence is a `var` node (`fixpt-fx26`'s `reps.rs`).
        let filled = fixpt_reps::fill::fill(rep, &given, "var").ok()?;
        filled.holes.is_empty().then_some(filled)
    }
}

static MADE: AtomicU64 = AtomicU64::new(0);

/// A region of its own: the evidence of a region constant by a name no
/// other has (`%region-N`; a program's begin `@`), as both checkers' reps
/// write one (`rconst`).
pub fn fresh_region() -> fixpt_reps::Rep {
    let name = format!("%region-{}", MADE.fetch_add(1, Ordering::Relaxed));
    let mut b = fixpt_reps::Builder::new();
    let s = b.name(&name);
    let r = b.add("rconst", &[], vec![fixpt_reps::Arg::Sym(s)]);
    let root = b.add(fixpt_reps::fill::EVIDENCE, &[], vec![fixpt_reps::Arg::Node(r)]);
    b.finish(root).expect("a region's evidence").rep
}

/// A bytevector's bytes; none if it is empty or none.
fn bytes_of(rt: &Runtime, b: Value) -> Option<Vec<u8>> {
    if !rt.heap.is_a(b, fixpt_heap::ObjType::Bytevector) || rt.heap.bytevector_len(b) == 0 {
        return None;
    }
    Some((0..rt.heap.bytevector_len(b)).map(|i| rt.heap.bytevector_ref(b, i)).collect())
}

/// What a `reify-…` makes of `rep`, the rep the checker noted of what it
/// is of (or none), its holes filled by the evidence `given`; a region of
/// its own's, if `fresh`; none if neither.
fn reify(rep: Option<fixpt_reps::Rep>, given: &Given, fresh: bool) -> Option<fixpt_reps::Rep> {
    if fresh {
        return Some(fresh_region());
    }
    given.filled(&rep?)
}

/// What the evaluator written in FX-26 makes of a `reify-…`
/// (`%fx26-reify-rep`): `rep`, the rep the checker noted (or `#f`), its
/// holes filled by the evidence `given` (their reps' binary forms) of the
/// variables `names`, in its binary form; a region of its own's if `fresh`
/// says so; empty if none.
pub fn reified_rep(rt: &mut Runtime, fresh: Value, rep: Value, names: Value, given: Value) -> Value {
    let fresh = rt.heap.string_to_rust(fresh) == "fresh";
    let given = Given::of_bytes(rt, names, given);
    let rep = fixpt_reps::heap::from_heap(&rt.heap, rep, true).ok();
    let bytes = reify(rep, &given, fresh).map(|r| fixpt_reps::binary::encode(&r)).unwrap_or_default();
    rt.heap.make_bytevector(&bytes)
}

/// What a `reify-…` makes (`%fx26-reify-effect` and the others): of
/// `staged`, the product the compilers make of its operand (`fresh` or "",
/// the operand, which is the evidence given it, the names it is evidence
/// of, and the rep of what it is of), the rep of what it is of, in the
/// heap, its holes filled by that evidence; or `#f`.
pub fn reified(rt: &mut Runtime, staged: Value) -> Value {
    if !(rt.heap.is_product(staged) && rt.heap.bloblet_len(staged) == 4) {
        return Value::FALSE;
    }
    let fresh = rt.heap.string_to_rust(rt.heap.product_field(staged, 1)) == "fresh";
    let given = Given::of(rt, rt.heap.product_field(staged, 3), rt.heap.product_field(staged, 2));
    let rep = fixpt_reps::heap::from_heap(&rt.heap, rt.heap.product_field(staged, 4), true).ok();
    match reify(rep, &given, fresh) {
        Some(r) => fixpt_reps::heap::to_heap(&mut rt.heap, &r),
        None => Value::FALSE,
    }
}
