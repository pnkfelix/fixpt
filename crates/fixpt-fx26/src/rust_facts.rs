//! What the checker written in Rust found of some forms, as the compiler
//! written in FX-26 reads it (`checked-extracts`, `checked-withs!`,
//! `checked-reshapes!`): each expression's facts, keyed by its identity as
//! the FX-26 parser makes it (`crate::ids`). Found as Rust data
//! ([`FormFacts::of`]), then made heap values in one go ([`FormFacts::facts`],
//! [`FormFacts::withs`], [`FormFacts::reshapes`]), by a session's driver
//! (`syn::rust_facts`) or the runtime alone (a session's code,
//! `sessions.rs`).

use crate::ast::ExpId;
use crate::check::{Checker, Datum};
use crate::top::Top;
use fixpt_heap::{Heap, Value};
use fixpt_read::FileId;
use std::collections::HashMap;

/// An expression's identity, as the product `k-at` is: where it starts and
/// ends, in characters, and which of the expressions there it is.
type At = (i64, i64, i64);

/// What a fact notes, as `k-noted` says it: its constructor's name and its
/// value.
enum Noted {
    None,
    Int(i64),
    Datum(Datum),
    /// A sum of no fields, by its constructor's name.
    Tag(&'static str),
}

/// What the checker found of the forms given, as the FX-26 compiler reads it.
pub struct FormFacts {
    facts: Vec<(At, &'static str, Noted)>,
    withs: Vec<(At, Vec<String>, Vec<i64>)>,
    reshapes: Vec<(At, Vec<(i64, Option<i64>)>)>,
}

/// Where module files' positions begin, each past the one before
/// (`syn.rs`'s `LOAD_BASE_STEP`).
const LOAD_BASE_STEP: i64 = 1_000_000_000;

fn byte_offsets(text: &str) -> Vec<usize> {
    let mut v: Vec<usize> = text.char_indices().map(|(i, _)| i).collect();
    v.push(text.len());
    v
}

impl FormFacts {
    /// Of `tops`, the forms of `text`, in `file`, as checker `c` checked
    /// them; with `only`, of their expressions alone (the checker holding
    /// others: a session's earlier forms, and a form checked again).
    pub fn of(c: &Checker, tops: &[&Top], file: FileId, text: &str, only: bool) -> FormFacts {
        let mut kth = crate::ids::Kth::new();
        for t in tops {
            kth.top(c, t);
        }
        let offsets = byte_offsets(text);
        let files: HashMap<FileId, Vec<usize>> = c.loaded.values().map(|(_, t, f)| (*f, byte_offsets(t))).collect();
        let at = |f: FileId, byte: u32| -> i64 {
            match files.get(&f) {
                Some(o) if f != file => LOAD_BASE_STEP * (f.0 as i64 - 1000) + o.partition_point(|&x| x < byte as usize) as i64,
                _ => offsets.partition_point(|&o| o < byte as usize) as i64,
            }
        };
        let place = |e: ExpId| {
            let span = c.arena.span_of(e);
            (at(span.file, span.start), at(span.file, span.end), kth.of(e) as i64)
        };
        let ours = |e: &ExpId| !only || kth.walked(*e);
        let mut facts: Vec<(At, &str, Noted)> = c.facts.datum.iter().filter(|(e, _)| ours(e)).map(|(e, d)| (place(*e), "n-datum", Noted::Datum(*d))).collect();
        // Each expression's effect summary: the greatest of its effects'.
        let mut summaries: HashMap<At, i64> = HashMap::new();
        for (e, s) in c.effect_summaries_by_exp() {
            if ours(&e) {
                let k = summaries.entry(place(e)).or_insert(s as i64);
                *k = (*k).max(s as i64);
            }
        }
        facts.extend(summaries.into_iter().map(|(at, s)| (at, "n-summary", Noted::Int(s))));
        // Each conversion, its code (`k-convert-at`).
        facts.extend(c.facts.converted.keys().filter(|e| ours(e)).filter_map(|e| c.facts.conversion_code(*e).map(|k| (place(*e), "n-conversion", Noted::Int(k)))));
        // Each `apply` of a list at `acyclic` (`k-note-apply-shares`).
        facts.extend(c.facts.apply_shares.iter().filter(|e| ours(e)).map(|e| (place(*e), "n-apply-shares", Noted::None)));
        // Each definition's value that is a list nothing writes.
        facts.extend(c.facts.frozen_defines.iter().filter(|e| ours(e)).map(|e| (place(*e), "n-frozen-define", Noted::None)));
        // Each `(with #%fx n)` that is the plain `n` (`k-synth-fx`).
        facts.extend(c.facts.fx_plain.keys().filter(|e| ours(e)).map(|e| (place(*e), "n-plain-fx", Noted::None)));
        // Each call's convention, a `k-conv` (`k-note-call`).
        facts.extend(c.facts.call_convs.keys().filter(|e| ours(e)).map(|e| {
            let cv = match c.facts.call_conv(*e) {
                crate::ast::Conv::Cellular => "cv-cellular",
                crate::ast::Conv::Native => "cv-native",
                _ => "cv-fx",
            };
            (place(*e), "n-call", Noted::Tag(cv))
        }));
        // Each `with`'s module's values it names, and their positions.
        let withs = c
            .facts
            .with_vals
            .iter()
            .filter(|(e, _)| ours(e))
            .map(|(e, names)| {
                (place(*e), names.iter().map(|(n, _)| c.interner.name(*n).to_string()).collect(), names.iter().map(|(_, i)| *i as i64).collect())
            })
            .collect();
        // Each module reshaped, with the positions it keeps.
        let reshapes = c
            .facts
            .reshaped
            .iter()
            .filter(|(e, _)| ours(e))
            .map(|(e, keep)| {
                let picks = keep
                    .iter()
                    .map(|k| match k.steps() {
                        (k, None) => (k as i64, None),
                        (k, Some(j)) => (k as i64, Some(j as i64)),
                    })
                    .collect();
                (place(*e), picks)
            })
            .collect();
        FormFacts { facts, withs, reshapes }
    }

    /// These, and `more`'s, of a text `by` characters past the start of
    /// theirs: so that the forms of several texts compile as one.
    pub fn and_after(mut self, more: FormFacts, by: i64) -> FormFacts {
        let shift = |(a, b, k): At| if a < LOAD_BASE_STEP { (a + by, b + by, k) } else { (a, b, k) };
        self.facts.extend(more.facts.into_iter().map(|(at, n, v)| (shift(at), n, v)));
        self.withs.extend(more.withs.into_iter().map(|(at, ns, is)| (shift(at), ns, is)));
        self.reshapes.extend(more.reshapes.into_iter().map(|(at, ps)| (shift(at), ps)));
        self
    }

    /// None.
    pub fn none() -> FormFacts {
        FormFacts { facts: Vec::new(), withs: Vec::new(), reshapes: Vec::new() }
    }

    /// The facts, a `k-facts`, the last found first, as `syn::rust_facts`
    /// always made them. Nothing collects as they are made.
    pub fn facts(&self, heap: &mut Heap) -> Value {
        let mut list = Value::NULL;
        for (at, noted, value) in self.facts.iter() {
            let at = identity(heap, *at);
            let fields = match value {
                Noted::None => Vec::new(),
                Noted::Int(n) => vec![Value::fixnum(*n)],
                Noted::Tag(name) => vec![sum(heap, name, &[])],
                // A `k-datum`, `parser-types.fx`'s.
                Noted::Datum(d) => {
                    let (name, ns) = match *d {
                        Datum::Field(i) => ("datum-field", vec![i as i64]),
                        Datum::BlobrefField(o) => ("datum-blobref-field", vec![o as i64]),
                        Datum::Layout(code) => ("datum-layout", vec![code as i64]),
                        Datum::Array { n, size } => ("datum-array", vec![n, size as i64]),
                        Datum::Fits(size) => ("datum-fits", vec![size as i64]),
                    };
                    let ns: Vec<Value> = ns.into_iter().map(Value::fixnum).collect();
                    vec![sum(heap, name, &ns)]
                }
            };
            let noted = sum(heap, noted, &fields);
            let fact = heap.make_frozen(PRODUCT, &[at, noted]);
            list = heap.cons(fact, list);
        }
        list
    }

    /// Each `with`'s noted values, a `k-with-list`.
    pub fn withs(&self, heap: &mut Heap) -> Value {
        let mut list = Value::NULL;
        for (at, names, is) in self.withs.iter() {
            let syms: Vec<Value> = names.iter().map(|n| heap.intern(n)).collect();
            let ns = heap.list_from(&syms);
            let is: Vec<Value> = is.iter().map(|i| Value::fixnum(*i)).collect();
            let is = heap.list_from(&is);
            let at = identity(heap, *at);
            let one = heap.make_frozen(PRODUCT, &[at, ns, is]);
            list = heap.cons(one, list);
        }
        list
    }

    /// Each module reshaped, a `k-reshape-list`.
    pub fn reshapes(&self, heap: &mut Heap) -> Value {
        let mut list = Value::NULL;
        for (at, picks) in self.reshapes.iter() {
            let mut ks = Value::NULL;
            // Each a `k-pick`, `check-env-types.fx`'s.
            for (k, j) in picks.iter().rev() {
                let pick = match j {
                    None => sum(heap, "pick-value", &[Value::fixnum(*k)]),
                    Some(j) => sum(heap, "pick-path", &[Value::fixnum(*k), Value::fixnum(*j)]),
                };
                ks = heap.cons(pick, ks);
            }
            let at = identity(heap, *at);
            let one = heap.make_frozen(PRODUCT, &[at, ks]);
            list = heap.cons(one, list);
        }
        list
    }
}

const PRODUCT: u8 = fixpt_heap::layout::kind("product");
const SUM: u8 = fixpt_heap::layout::kind("sum");

/// An identity, as the product `k-at` is.
fn identity(heap: &mut Heap, (a, b, k): At) -> Value {
    heap.make_frozen(PRODUCT, &[Value::fixnum(a), Value::fixnum(b), Value::fixnum(k)])
}

/// A datatype's value: a sum of its constructor's name and the product of
/// its fields.
fn sum(heap: &mut Heap, name: &str, fields: &[Value]) -> Value {
    let fields = heap.make_frozen(PRODUCT, fields);
    let name = heap.intern(name);
    heap.make_frozen(SUM, &[name, fields])
}
