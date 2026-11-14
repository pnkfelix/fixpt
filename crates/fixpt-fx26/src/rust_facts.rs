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
use fixpt_hash::HashMap;

/// An expression's identity, as the product `k-at` is: where it starts and
/// ends, in characters, and its place in the walk of the forms
/// (`ids::Kth`), which the compiler makes the key the FX-26 parser gave
/// there (`c-absolute-at`).
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
    /// How many expressions the walk took.
    walked: i64,
}

/// Where module files' positions begin, each past the one before
/// (`syn.rs`'s `LOAD_BASE_STEP`).
const LOAD_BASE_STEP: i64 = 1_000_000_000;

impl FormFacts {
    /// Of `tops`, the forms of `text`, in `file`, as checker `c` checked
    /// them; with `only`, of their expressions alone (the checker holding
    /// others: a session's earlier forms, and a form checked again).
    pub fn of(c: &Checker, tops: &[&Top], file: FileId, _text: &str, only: bool) -> FormFacts {
        let mut kth = crate::ids::Kth::new();
        for t in tops {
            kth.top(c, t);
        }
        // Looked up twice a fact, hundreds of thousands of times for the
        // front end: by `IdHasher`, not SipHash (the Mac team's profile,
        // `TODO.md` §257, some 6%). A span is in characters, as FX-26's
        // positions are (`crate::chars`): a loaded file's past its base.
        let files: crate::ast::IdMap<FileId, ()> = c.loaded.values().map(|(_, _, f)| (*f, ())).collect();
        let at = |f: FileId, ch: u32| -> i64 {
            match files.get(&f) {
                Some(()) if f != file => LOAD_BASE_STEP * (f.0 as i64 - 1000) + ch as i64,
                _ => ch as i64,
            }
        };
        let place = |e: ExpId| {
            let span = c.arena.span_of(e);
            (at(span.file, span.start), at(span.file, span.end), kth.of(e) as i64)
        };
        let ours = |e: &ExpId| !only || kth.walked(*e);
        let mut facts: Vec<(At, &str, Noted)> = c.facts.datum.iter().filter(|(e, _)| ours(e)).map(|(e, d)| (place(*e), "n-datum", Noted::Datum(*d))).collect();
        // Each expression's effect summary: the greatest of its effects'.
        let mut summaries: HashMap<At, i64> = HashMap::default();
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
        FormFacts { facts, withs, reshapes, walked: kth.count() as i64 }
    }

    /// These, and `more`'s, of a text `by` characters past the start of
    /// theirs, and their walk after this one's: so that the forms of several
    /// texts compile as one.
    pub fn and_after(mut self, more: FormFacts, by: i64) -> FormFacts {
        let walked = self.walked;
        let shift = |(a, b, k): At| if a < LOAD_BASE_STEP { (a + by, b + by, k + walked) } else { (a, b, k + walked) };
        self.facts.extend(more.facts.into_iter().map(|(at, n, v)| (shift(at), n, v)));
        self.withs.extend(more.withs.into_iter().map(|(at, ns, is)| (shift(at), ns, is)));
        self.reshapes.extend(more.reshapes.into_iter().map(|(at, ps)| (shift(at), ps)));
        self.walked += more.walked;
        self
    }

    /// How many expressions the walk of these forms took: how many the
    /// FX-26 parser numbers of them.
    pub fn walked(&self) -> i64 {
        self.walked
    }

    /// None.
    pub fn none() -> FormFacts {
        FormFacts { facts: Vec::new(), withs: Vec::new(), reshapes: Vec::new(), walked: 0 }
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

/// Every name a fact notes, or a tag it holds: what one read back
/// ([`FormFacts::from_bytes`]) is one of.
const NAMES: [&str; 10] = ["n-datum", "n-summary", "n-conversion", "n-apply-shares", "n-frozen-define", "n-plain-fx", "n-call", "cv-cellular", "cv-native", "cv-fx"];

impl FormFacts {
    /// These as bytes, for the cache of what checking a text found
    /// (`facts_cache`): read back by [`from_bytes`](Self::from_bytes).
    pub(crate) fn to_bytes(&self) -> Vec<u8> {
        let mut out = Bytes(Vec::new());
        out.int(self.walked);
        out.int(self.facts.len() as i64);
        for (at, noted, value) in &self.facts {
            out.at(*at);
            out.str(noted);
            match value {
                Noted::None => out.int(0),
                Noted::Int(n) => {
                    out.int(1);
                    out.int(*n);
                }
                Noted::Tag(t) => {
                    out.int(2);
                    out.str(t);
                }
                Noted::Datum(d) => {
                    out.int(3);
                    let (k, a, b) = match *d {
                        Datum::Field(i) => (0, i as i64, 0),
                        Datum::BlobrefField(o) => (1, o as i64, 0),
                        Datum::Layout(c) => (2, c as i64, 0),
                        Datum::Array { n, size } => (3, n, size as i64),
                        Datum::Fits(size) => (4, size as i64, 0),
                    };
                    [k, a, b].into_iter().for_each(|n| out.int(n));
                }
            }
        }
        out.int(self.withs.len() as i64);
        for (at, names, is) in &self.withs {
            out.at(*at);
            out.int(names.len() as i64);
            names.iter().for_each(|n| out.str(n));
            out.int(is.len() as i64);
            is.iter().for_each(|i| out.int(*i));
        }
        out.int(self.reshapes.len() as i64);
        for (at, picks) in &self.reshapes {
            out.at(*at);
            out.int(picks.len() as i64);
            for (k, j) in picks {
                out.int(*k);
                out.int(j.unwrap_or(-1));
            }
        }
        out.0
    }

    /// What [`to_bytes`](Self::to_bytes) made; none if `bytes` is not that.
    pub(crate) fn from_bytes(bytes: &[u8]) -> Option<FormFacts> {
        let mut r = Reader(bytes);
        let walked = r.int()?;
        let mut facts = Vec::new();
        for _ in 0..r.count()? {
            let at = r.at()?;
            let noted = r.name()?;
            let value = match r.int()? {
                0 => Noted::None,
                1 => Noted::Int(r.int()?),
                2 => Noted::Tag(r.name()?),
                3 => {
                    let (k, a, b) = (r.int()?, r.int()?, r.int()?);
                    Noted::Datum(match k {
                        0 => Datum::Field(a as usize),
                        1 => Datum::BlobrefField(a as usize),
                        2 => Datum::Layout(a as usize),
                        3 => Datum::Array { n: a, size: b as usize },
                        4 => Datum::Fits(a as usize),
                        _ => return None,
                    })
                }
                _ => return None,
            };
            facts.push((at, noted, value));
        }
        let mut withs = Vec::new();
        for _ in 0..r.count()? {
            let at = r.at()?;
            let names = (0..r.count()?).map(|_| r.str()).collect::<Option<Vec<_>>>()?;
            let is = (0..r.count()?).map(|_| r.int()).collect::<Option<Vec<_>>>()?;
            withs.push((at, names, is));
        }
        let mut reshapes = Vec::new();
        for _ in 0..r.count()? {
            let at = r.at()?;
            let picks = (0..r.count()?).map(|_| Some((r.int()?, Some(r.int()?).filter(|j| *j >= 0)))).collect::<Option<Vec<_>>>()?;
            reshapes.push((at, picks));
        }
        r.0.is_empty().then_some(FormFacts { facts, withs, reshapes, walked })
    }
}

/// Bytes being written: each integer eight, little-endian; each string its
/// length, then it.
struct Bytes(Vec<u8>);

impl Bytes {
    fn int(&mut self, n: i64) {
        self.0.extend_from_slice(&n.to_le_bytes());
    }
    fn at(&mut self, (a, b, k): At) {
        [a, b, k].into_iter().for_each(|n| self.int(n));
    }
    fn str(&mut self, s: &str) {
        self.int(s.len() as i64);
        self.0.extend_from_slice(s.as_bytes());
    }
}

/// [`Bytes`] read back.
struct Reader<'a>(&'a [u8]);

impl Reader<'_> {
    fn int(&mut self) -> Option<i64> {
        let (n, rest) = self.0.split_first_chunk::<8>()?;
        self.0 = rest;
        Some(i64::from_le_bytes(*n))
    }
    fn count(&mut self) -> Option<usize> {
        usize::try_from(self.int()?).ok().filter(|n| *n <= self.0.len())
    }
    fn at(&mut self) -> Option<At> {
        Some((self.int()?, self.int()?, self.int()?))
    }
    fn str(&mut self) -> Option<String> {
        let n = self.count()?;
        let (s, rest) = self.0.split_at(n);
        self.0 = rest;
        String::from_utf8(s.to_vec()).ok()
    }
    fn name(&mut self) -> Option<&'static str> {
        let s = self.str()?;
        NAMES.iter().find(|n| **n == s).copied()
    }
}

const PRODUCT: u8 = fixpt_heap::layout::kind("product");
const SUM: u8 = fixpt_heap::layout::kind("sum");

/// An identity, as the product `k-at` is: of reading -1, its number its
/// place in the walk, the key the FX-26 parser gives there not known yet,
/// which the compiler gives it (`c-absolute-at`).
fn identity(heap: &mut Heap, (a, b, k): At) -> Value {
    heap.make_frozen(PRODUCT, &[Value::fixnum(a), Value::fixnum(b), Value::fixnum(k), Value::fixnum(-1)])
}

/// A datatype's value: a sum of its constructor's name and the product of
/// its fields.
fn sum(heap: &mut Heap, name: &str, fields: &[Value]) -> Value {
    let fields = heap.make_frozen(PRODUCT, fields);
    let name = heap.intern(name);
    heap.make_frozen(SUM, &[name, fields])
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Facts of every kind, written and read back, are what they were (as
    /// written again), and bytes cut short are none.
    #[test]
    fn facts_are_kept_as_they_were() {
        let facts = FormFacts {
            facts: vec![
                ((0, 5, 1), "n-datum", Noted::Datum(Datum::Field(3))),
                ((1, 4, 2), "n-datum", Noted::Datum(Datum::BlobrefField(16))),
                ((2, 3, 3), "n-datum", Noted::Datum(Datum::Layout(7))),
                ((3, 9, 4), "n-datum", Noted::Datum(Datum::Array { n: -1, size: 8 })),
                ((4, 9, 5), "n-datum", Noted::Datum(Datum::Fits(24))),
                ((5, 6, 6), "n-summary", Noted::Int(2)),
                ((6, 7, 7), "n-apply-shares", Noted::None),
                ((7, 8, 8), "n-call", Noted::Tag("cv-native")),
            ],
            withs: vec![((10, 20, 9), vec!["car".into(), "a name with spaces".into()], vec![0, 4])],
            reshapes: vec![((30, 40, 10), vec![(1, None), (2, Some(5))])],
            walked: 11,
        };
        let bytes = facts.to_bytes();
        let back = FormFacts::from_bytes(&bytes).expect("read back");
        assert_eq!(back.to_bytes(), bytes);
        assert_eq!(back.walked(), 11);
        assert!(FormFacts::from_bytes(&bytes[..bytes.len() - 1]).is_none(), "cut short");
        let mut more = bytes.clone();
        more.push(0);
        assert!(FormFacts::from_bytes(&more).is_none(), "with more after");
    }
}
