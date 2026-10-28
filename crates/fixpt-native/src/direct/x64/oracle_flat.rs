//! The Rust compiler's heap pieces by name (`flat_count` to `flat_set`, and
//! `shape_fast`), for `super::oracle`: each run on a fresh `Asm`, the
//! labels it is given (`slow`, then `done` or `wide`) made before it and
//! bound after it, in that order, an `int3` after them. None of them
//! numbers a call-out; for `shape-fast`, the call-outs are one number, 1 if
//! it knew the shape, else 0.

use super::*;

/// The shape predicates `shape-fast` is given, by index: those it knows,
/// and one it does not.
pub const SHAPES: [&str; 14] = [
    "null?",
    "pair?",
    "char?",
    "%fx26-f32?",
    "boolean?",
    "exact-integer?",
    "symbol?",
    "string?",
    "%fx26-array?",
    "%fx26-box?",
    "%fx26-one?",
    "%fx26-tup?",
    "%fx26-procedure?",
    "%fx26-nothing-in-line?",
];

/// The bytes piece `name` emits given `args`, and the call-outs it numbers;
/// none for a name this does not know.
pub(super) fn oracle(name: &str, args: &[i64]) -> Option<(Vec<u8>, Vec<i64>)> {
    let mut a = Asm::new();
    let (slow, other) = (a.label(), a.label());
    let r = |k: usize| args[k] as Reg;
    let b = |k: usize| args[k] != 0;
    let mut known = Vec::new();
    match name {
        "flat-count" => flat_count(&mut a, r(0), r(1)),
        "flat-element" => flat_element(&mut a, r(0), r(1), slow),
        "flat-ref" => flat_ref(&mut a, r(0), slow),
        "suffix-owner" => suffix_owner(&mut a, r(0), slow),
        "suffix-writable" => suffix_writable(&mut a, r(0), slow),
        "suffix-store" => suffix_store(&mut a, args[0], r(1), b(2), slow),
        "blobref-index" => blobref_index(&mut a, args[0], r(1), slow),
        "flat-variant" => flat_variant(&mut a, args[0], r(1), slow),
        "blobref-at" => blobref_at(&mut a, args[0], slow),
        "suffix-step" => suffix_step(&mut a, args[0], slow),
        "suffix-fits" => suffix_fits(&mut a, args[0], slow),
        "suffix-length" => suffix_length(&mut a, args[0], slow),
        "suffix-index" => suffix_index(&mut a, slow),
        "flat-tag" => flat_tag(&mut a, args[0], slow),
        "suffix-get" => suffix_get(&mut a, args[0], b(1), slow),
        "wide-layout" => wide_layout(&mut a, r(0), other),
        "suffix-set" => suffix_set(&mut a, slow, other),
        "bytes-set" => bytes_set(&mut a, slow, other),
        "flat-set" => flat_set(&mut a, slow, other, b(0)),
        "shape-fast" => known.push(shape_fast(&mut a, SHAPES[args[0] as usize], slow) as i64),
        _ => return None,
    }
    a.bind(slow);
    a.bind(other);
    // Something after the labels, as there always is, for `finish` to read.
    a.e(int3());
    Some((a.finish().expect("placed"), known))
}
