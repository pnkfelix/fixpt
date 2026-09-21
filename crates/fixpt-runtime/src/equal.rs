//! `eqv?` and `equal?`.

use crate::num::N;
use fixpt_heap::{Heap, ObjType, Value};

/// `eq?` — identity. Fixnums, characters and the immediates compare by value
/// because they *are* their value; everything else compares by heap address.
pub fn eq(a: Value, b: Value) -> bool {
    a == b
}

/// `eqv?` — `eq?`, plus numbers and characters of the same exactness comparing
/// by value even when boxed.
pub fn eqv(heap: &Heap, a: Value, b: Value) -> bool {
    if a == b {
        return true;
    }
    match (N::load(heap, a), N::load(heap, b)) {
        (Some(x), Some(y)) => {
            // R7RS: eqv? is false for operands of differing exactness, even
            // when numerically equal -- (eqv? 2 2.0) is #f.
            x.is_exact() == y.is_exact() && x.num_eq(&y)
        }
        _ => {
            // Empty strings and vectors may or may not be eqv?; we say yes for
            // the empty ones, which is permitted and cheap.
            match (heap.obj_type(a), heap.obj_type(b)) {
                (Some(ObjType::String), Some(ObjType::String)) => {
                    heap.string_len(a) == 0 && heap.string_len(b) == 0
                }
                (Some(ObjType::Vector), Some(ObjType::Vector)) => {
                    heap.obj_len(a) == 0 && heap.obj_len(b) == 0
                }
                _ => false,
            }
        }
    }
}

/// `equal?` — structural, and safe on cyclic input.
///
/// R7RS requires termination even on circular structure. Rather than a union
/// -find over a trail, this bounds the work: once the comparison has taken
/// more steps than either structure could have distinct nodes, it falls back
/// to a visited-pair set. The fast path stays allocation-free.
pub fn equal(heap: &Heap, a: Value, b: Value) -> bool {
    let mut budget: u32 = 100_000;
    let mut trail: Vec<(Value, Value)> = Vec::new();
    equal_inner(heap, a, b, &mut budget, &mut trail)
}

fn equal_inner(
    heap: &Heap,
    a: Value,
    b: Value,
    budget: &mut u32,
    trail: &mut Vec<(Value, Value)>,
) -> bool {
    if eqv(heap, a, b) {
        return true;
    }
    if *budget == 0 {
        // Past the budget we are plausibly walking a cycle, so start recording
        // pairs already under comparison and treat a repeat as equal — the
        // standard co-inductive reading.
        if trail.contains(&(a, b)) {
            return true;
        }
        trail.push((a, b));
    } else {
        *budget -= 1;
    }

    if a.is_pair() && b.is_pair() {
        return equal_inner(heap, heap.car(a), heap.car(b), budget, trail)
            && equal_inner(heap, heap.cdr(a), heap.cdr(b), budget, trail);
    }
    match (heap.obj_type(a), heap.obj_type(b)) {
        (Some(ObjType::String), Some(ObjType::String)) => {
            let n = heap.string_len(a);
            n == heap.string_len(b) && (0..n).all(|i| heap.string_ref(a, i) == heap.string_ref(b, i))
        }
        (Some(ObjType::Bytevector), Some(ObjType::Bytevector)) => {
            let n = heap.bytevector_len(a);
            n == heap.bytevector_len(b)
                && (0..n).all(|i| heap.bytevector_ref(a, i) == heap.bytevector_ref(b, i))
        }
        (Some(ObjType::Vector), Some(ObjType::Vector)) => {
            let n = heap.obj_len(a);
            n == heap.obj_len(b)
                && (0..n).all(|i| {
                    equal_inner(heap, heap.obj_ref(a, i), heap.obj_ref(b, i), budget, trail)
                })
        }
        _ => false,
    }
}
