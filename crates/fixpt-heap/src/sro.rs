//! SRO, "standing room only", after Larceny's (`src/Rts/Sys/sro.c`, Lars
//! Hansen, 1998): every live object of a kind, with how many references
//! reach it. A tool for looking at the heap from outside a program, as a
//! debugger does, and deliberately not part of any language's semantics: it
//! sees every region, private ones included.
//!
//! It traces from the heap's own roots (explicit roots, globals, symbols).
//! An engine's stack is not among them, so an object only a running
//! procedure's frame holds is not found.

use crate::layout::TAG_MASK;
use crate::value::TAG_TRAILER;
use crate::{Heap, Value};
use std::collections::HashMap;

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
    pub fn sro(&self, kind: SroKind, limit: Option<usize>) -> Vec<Value> {
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
        while let Some(v) = todo.pop() {
            if v.is_pair() {
                reach(self.car(v), &mut counts, &mut todo);
                reach(self.cdr(v), &mut counts, &mut todo);
            } else {
                let fields = self.bloblet_head(v).fields;
                for k in 1..=fields {
                    let w = self.word(v.index() - k);
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
}
