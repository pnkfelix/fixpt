//! SRO, "standing room only", after Larceny's (`src/Rts/Sys/sro.c`, Lars
//! Hansen, 1998): every live object of a kind, with how many references
//! reach it. A tool for looking at the heap from outside a program, as a
//! debugger does, and deliberately not part of any language's semantics: it
//! sees every region, private ones included.
//!
//! It traces from the heap's own roots (explicit roots, globals, symbols)
//! and whatever roots the caller adds: an engine's stacks, which only the
//! engine has, so `%sro` is an engine operation.

use crate::layout::TAG_MASK;
use crate::value::TAG_TRAILER;
use crate::{Heap, Value};
use std::collections::HashMap;

/// Who refers to an object, as [`Heap::sro_referrers`] says.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Referrers {
    /// At most the limit asked for: each.
    Few(Vec<Referrer>),
    /// More than the limit.
    Many,
}

/// One reference to an object: from a root, or from a field of a live
/// object (for a pair, 1 is its `car` and 2 its `cdr`).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Referrer {
    /// The heap's explicit root at this index.
    Root(usize),
    /// The heap's global at this index.
    Global(usize),
    /// The heap's symbol at this index.
    Symbol(usize),
    /// Extra root `i` of extra slice `s`.
    Extra(usize, usize),
    /// Field `k` of this object.
    Field(Value, usize),
}

/// Which objects to report.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum SroKind {
    Any,
    Pair,
    /// Bloblets of this kind (`layout::KINDS`).
    Kind(u8),
}

impl Heap {
    /// Every live object of `kind` reached by at least 1 and at most
    /// `limit` references (from roots or live objects), each once, in no
    /// particular order.
    pub fn sro(&self, kind: SroKind, limit: Option<usize>, extra_roots: &[&[Value]]) -> Vec<Value> {
        // Reference counts, by Value; each object's edges are followed once.
        let mut counts: HashMap<u64, usize> = HashMap::new();
        let mut todo: Vec<Value> = Vec::new();
        let reach = |v: Value, counts: &mut HashMap<u64, usize>, todo: &mut Vec<Value>| {
            if !v.is_ref() {
                return;
            }
            let n = counts.entry(v.raw()).or_insert(0);
            *n += 1;
            if *n == 1 {
                todo.push(v);
            }
        };
        for v in self.roots_for_sro() {
            reach(v, &mut counts, &mut todo);
        }
        for slice in extra_roots {
            for v in *slice {
                reach(*v, &mut counts, &mut todo);
            }
        }
        while let Some(v) = todo.pop() {
            if v.is_pair() {
                reach(self.car(v), &mut counts, &mut todo);
                reach(self.cdr(v), &mut counts, &mut todo);
            } else {
                let fields = self.bloblet_head(v).fields;
                for k in 1..=fields {
                    let w = self.word(self.ix(v) - k);
                    if w & TAG_MASK != TAG_TRAILER {
                        reach(Value(w), &mut counts, &mut todo);
                    }
                }
            }
        }
        counts
            .into_iter()
            .filter(|(_, n)| limit.is_none_or(|l| *n <= l))
            .map(|(raw, _)| Value(raw))
            .filter(|v| match kind {
                SroKind::Any => true,
                SroKind::Pair => v.is_pair(),
                SroKind::Kind(k) => v.is_bloblet() && self.bloblet_kind(*v) == k,
            })
            .collect()
    }

    /// Every live object (of `kind`) with who refers to it: up to `limit`
    /// referrers each, as [`Referrer`]s, or [`Referrers::Many`] past that.
    /// The trace is [`sro`](Heap::sro)'s: the heap's roots and
    /// `extra_roots`. For finding why something is alive, from the other end
    /// than `sro`'s counts: walk the referrers back to a root.
    pub fn sro_referrers(&self, kind: SroKind, limit: usize, extra_roots: &[&[Value]]) -> HashMap<u64, Referrers> {
        let mut seen: HashMap<u64, Referrers> = HashMap::new();
        let mut todo: Vec<Value> = Vec::new();
        let reach = |v: Value, by: Referrer, seen: &mut HashMap<u64, Referrers>, todo: &mut Vec<Value>| {
            if !v.is_ref() {
                return;
            }
            match seen.get_mut(&v.raw()) {
                None => {
                    seen.insert(v.raw(), Referrers::Few(vec![by]));
                    todo.push(v);
                }
                Some(Referrers::Few(rs)) if rs.len() < limit => rs.push(by),
                Some(r @ Referrers::Few(_)) => *r = Referrers::Many,
                Some(Referrers::Many) => {}
            }
        };
        let (r, g) = (self.roots_slice().len(), self.globals_slice().len());
        for (i, v) in self.roots_for_sro().into_iter().enumerate() {
            let by = if i < r {
                Referrer::Root(i)
            } else if i < r + g {
                Referrer::Global(i - r)
            } else {
                Referrer::Symbol(i - r - g)
            };
            reach(v, by, &mut seen, &mut todo);
        }
        for (s, slice) in extra_roots.iter().enumerate() {
            for (i, v) in slice.iter().enumerate() {
                reach(*v, Referrer::Extra(s, i), &mut seen, &mut todo);
            }
        }
        while let Some(v) = todo.pop() {
            if v.is_pair() {
                reach(self.car(v), Referrer::Field(v, 1), &mut seen, &mut todo);
                reach(self.cdr(v), Referrer::Field(v, 2), &mut seen, &mut todo);
            } else {
                let fields = self.bloblet_head(v).fields;
                for k in 1..=fields {
                    let w = self.word(self.ix(v) - k);
                    if w & TAG_MASK != TAG_TRAILER {
                        reach(Value(w), Referrer::Field(v, k), &mut seen, &mut todo);
                    }
                }
            }
        }
        seen.retain(|raw, _| match kind {
            SroKind::Any => true,
            SroKind::Pair => Value(*raw).is_pair(),
            SroKind::Kind(k) => Value(*raw).is_bloblet() && self.bloblet_kind(Value(*raw)) == k,
        });
        seen
    }

    /// Why `target` is alive: a chain of references to it from a root, as
    /// [`sro`](Heap::sro) traces (the heap's roots, and `extra_roots`), the
    /// shortest such chain; each step said as where it is (a root, a field,
    /// `car` or `cdr`) and what it is. `None` if nothing reaches it.
    pub fn path_to(&self, target: Value, extra_roots: &[&[Value]]) -> Option<Vec<String>> {
        // Each object reached, with the one it was first reached from and
        // through what; breadth first, so the chain found is a shortest.
        let mut from: HashMap<u64, (Option<u64>, String)> = HashMap::new();
        let mut todo = std::collections::VecDeque::new();
        let (r, g) = (self.roots_slice().len(), self.globals_slice().len());
        let roots = self.roots_for_sro();
        let starts = roots.iter().enumerate().map(|(i, v)| {
            let how = if i < r {
                format!("explicit root {i}")
            } else if i < r + g {
                format!("global {}", i - r)
            } else {
                format!("symbol {}", i - r - g)
            };
            (how, *v)
        });
        let extra = extra_roots.iter().enumerate().flat_map(|(s, vs)| vs.iter().enumerate().map(move |(i, v)| (format!("extra root {s}.{i}"), *v)));
        for (how, v) in starts.chain(extra) {
            if v.is_ref() && !from.contains_key(&v.raw()) {
                from.insert(v.raw(), (None, how));
                todo.push_back(v);
            }
        }
        while let Some(v) = todo.pop_front() {
            if v.raw() == target.raw() {
                let mut chain = Vec::new();
                let mut at = Some(v.raw());
                while let Some(raw) = at {
                    let (prev, how) = &from[&raw];
                    chain.push(format!("{how}: {}", self.describe(Value(raw))));
                    at = *prev;
                }
                chain.reverse();
                return Some(chain);
            }
            let mut edge = |how: String, w: Value| {
                if w.is_ref() && !from.contains_key(&w.raw()) {
                    from.insert(w.raw(), (Some(v.raw()), how));
                    todo.push_back(w);
                }
            };
            if v.is_pair() {
                edge("car".into(), self.car(v));
                edge("cdr".into(), self.cdr(v));
            } else {
                let fields = self.bloblet_head(v).fields;
                for k in 1..=fields {
                    let w = self.word(self.ix(v) - k);
                    if w & TAG_MASK != TAG_TRAILER {
                        edge(format!("field {k}"), Value(w));
                    }
                }
            }
        }
        None
    }

    /// An object, briefly: a pair, or a bloblet's kind, with its name if it
    /// is a symbol or a cellular word.
    pub fn describe(&self, v: Value) -> String {
        if v.is_pair() {
            return "a pair".into();
        }
        let kind = self.bloblet_kind(v);
        let name = crate::layout::KINDS.iter().find(|k| k.code == kind).map_or("?", |k| k.name);
        if name == "symbol" {
            format!("symbol `{}`", self.symbol_name(v))
        } else if self.is_cellular_word(v) {
            let n = self.bloblet_slot(v, crate::layout::cellular::WORD_NAME);
            let n = if n.is_bloblet() && self.bloblet_kind(n) == crate::layout::kind("symbol") { self.symbol_name(n) } else { "?".into() };
            format!("a cellular word `{n}`")
        } else {
            let fields = self.bloblet_head(v).fields;
            // A symbol among its fields: often what names it (a global's cell).
            let named = (1..=fields.min(8)).find_map(|k| {
                let raw = self.word(self.ix(v) - k);
                let w = Value(raw);
                (raw & TAG_MASK != TAG_TRAILER && w.is_bloblet() && self.bloblet_kind(w) == crate::layout::kind("symbol"))
                    .then(|| self.symbol_name(w))
            });
            match named {
                Some(n) => format!("a {name} of {fields} fields, naming `{n}`"),
                None => format!("a {name} of {fields} fields"),
            }
        }
    }
}
