//! The heap's fast paths of the native convention's compiler to arm64
//! written in FX-26 (`src/native-direct-arm64-flat.fx`) against the Rust
//! ones (`fixpt_native::direct::oracle_arm64`), piece by piece: the same
//! bytes, over every register a piece may be given, every layout and code,
//! and every shape predicate, with names it does not know. Any machine
//! compiles for arm64; none runs the code here.

#[path = "native-direct-arm64/harness.rs"]
mod harness;

use harness::{Case, Wrapper, A};

const MODULES: &str = include_str!("native-direct-arm64/flat-modules.fx");

/// Each piece given `slow` (`l0`) and `done` (`l1`), as the oracle's are.
const WRAPPERS: &[Wrapper] = &[
    ("flat-count", &[("arr", "int"), ("out", "int")], 2, "(adf-flat-count arr out)"),
    ("flat-element", &[("arr", "int"), ("y", "int")], 2, "(adf-flat-element arr y l0)"),
    ("flat-ref", &[("y", "int")], 2, "(adf-flat-ref y l0)"),
    ("box-bits", &[], 2, "(adf-box-bits l0)"),
    ("suffix-owner", &[("r", "int")], 2, "(adf-suffix-owner r l0)"),
    ("suffix-writable", &[("r", "int")], 2, "(adf-suffix-writable r l0)"),
    ("suffix-store", &[("code", "int"), ("v", "int"), ("raw", "bool")], 2, "(adf-suffix-store code v raw l0)"),
    ("blobref-index", &[("code", "int"), ("i", "int")], 2, "(adf-blobref-index code i l0)"),
    ("flat-variant", &[("code", "int"), ("l", "int")], 2, "(adf-flat-variant code l l0)"),
    ("blobref-at", &[("d", "int")], 2, "(adf-blobref-at d l0)"),
    ("suffix-step", &[("d", "int")], 2, "(adf-suffix-step d l0)"),
    ("suffix-fits", &[("size", "int")], 2, "(adf-suffix-fits size l0)"),
    ("suffix-length", &[("code", "int")], 2, "(adf-suffix-length code l0)"),
    ("suffix-index", &[], 2, "(adf-suffix-index l0)"),
    ("flat-tag", &[("code", "int")], 2, "(adf-flat-tag code l0)"),
    ("suffix-get", &[("code", "int"), ("raw", "bool")], 2, "(adf-suffix-get code raw l0)"),
    ("suffix-set", &[], 2, "(adf-suffix-set l0 l1)"),
    ("bytes-set", &[], 2, "(adf-bytes-set l0 l1)"),
    ("flat-set", &[("raw", "bool")], 2, "(adf-flat-set l0 l1 raw)"),
];

/// `shape-fast`, which answers whether it knew the shape (`pre`).
const EXTRA: &str = include_str!("native-direct-arm64/flat-extra.fx");

const PIECES: [&str; 20] = [
    "flat-count",
    "flat-element",
    "flat-ref",
    "box-bits",
    "suffix-owner",
    "suffix-writable",
    "suffix-store",
    "blobref-index",
    "flat-variant",
    "blobref-at",
    "suffix-step",
    "suffix-fits",
    "suffix-length",
    "suffix-index",
    "flat-tag",
    "suffix-get",
    "suffix-set",
    "bytes-set",
    "flat-set",
    "shape-fast",
];

/// The shape predicates: those `shape_fast` knows, and some it does not.
const SHAPES: [&str; 17] = [
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
    "%fx26-sum?",
    "%fx26-product?",
    "%fx26-procedure?",
    "%fx26-nothing-in-line?",
    "vector?",
    "",
    "null",
];

/// The flat layouts, the scalars' codes.
const LAYOUTS: [i64; 6] = [0, 1, 2, 3, 4, 5];

/// Array operands (`layout::array_operand`): lengths, the last running to
/// the end, by element sizes, powers of two and not.
fn array_operands() -> Vec<i64> {
    let mut out = Vec::new();
    for n in [0i64, 1, 3, 1000, 0xffff, 0x1_0000, fixpt_heap::layout::FLAT_TO_THE_END - 1, fixpt_heap::layout::FLAT_TO_THE_END] {
        for size in [1i64, 2, 4, 8, 12, 24, 3, 4096, 0x1_0001] {
            out.push((n << fixpt_heap::layout::ARRAY_OPERAND_LENGTH_SHIFT) | size);
        }
    }
    out
}

/// Flat sums' codes: a tag's width (1, 2 or 4 bytes, and the others
/// `code & 7` may be), numeric or not, and where the payload is.
fn sum_codes() -> Vec<i64> {
    let mut out = Vec::new();
    for w in [1i64, 2, 4, 3, 7] {
        for numeric in [0i64, 8] {
            for p in [0i64, 3, 200, 4096, 0x1_0000] {
                out.push(w | numeric | p << 8);
            }
        }
    }
    out
}

fn names() -> Vec<(String, &'static str)> {
    PIECES.iter().map(|p| (format!("adf-{p}"), "flat")).collect()
}

#[test]
fn every_heap_piece_as_the_rust_compiler_makes_it() {
    let names = names();
    let names: Vec<(&str, &str)> = names.iter().map(|(n, m)| (n.as_str(), *m)).collect();
    let program = harness::program(MODULES, &names, WRAPPERS, EXTRA);
    let mut s = harness::session(&program);
    let mut cases: Vec<Case> = Vec::new();
    let mut add = |name: &'static str, fx: Vec<A>, rust: Vec<i64>| cases.push((name, fx, rust));
    use A::{B, I, S};
    let regs: Vec<i64> = (0..31).collect();
    for &x in &regs {
        for &y in &regs {
            add("flat-count", vec![I(x), I(y)], vec![x, y]);
            add("flat-element", vec![I(x), I(y)], vec![x, y]);
        }
        add("flat-ref", vec![I(x)], vec![x]);
        add("suffix-owner", vec![I(x)], vec![x]);
        add("suffix-writable", vec![I(x)], vec![x]);
        for code in LAYOUTS {
            for raw in [false, true] {
                add("suffix-store", vec![I(code), I(x), B(raw)], vec![code, x, raw as i64]);
            }
        }
        for code in array_operands() {
            add("blobref-index", vec![I(code), I(x)], vec![code, x]);
        }
        for code in sum_codes() {
            add("flat-variant", vec![I(code), I(x)], vec![code, x]);
        }
    }
    add("box-bits", vec![], vec![]);
    for d in [0i64, 1, 8, 1000, 0xffff, 0x1_0000, (1 << 24) - 1, (1 << 26) - 1, (1 << 27) + 5, 1 << 40] {
        add("blobref-at", vec![I(d)], vec![d]);
        add("suffix-step", vec![I(d)], vec![d]);
        add("suffix-fits", vec![I(d)], vec![d]);
    }
    for code in array_operands() {
        add("suffix-length", vec![I(code)], vec![code]);
    }
    for code in sum_codes() {
        add("flat-tag", vec![I(code)], vec![code]);
    }
    for code in LAYOUTS {
        for raw in [false, true] {
            add("suffix-get", vec![I(code), B(raw)], vec![code, raw as i64]);
        }
    }
    add("suffix-index", vec![], vec![]);
    add("suffix-set", vec![], vec![]);
    add("bytes-set", vec![], vec![]);
    for raw in [false, true] {
        add("flat-set", vec![B(raw)], vec![raw as i64]);
    }
    for name in SHAPES {
        add("shape-fast", vec![S(name)], name.bytes().map(i64::from).collect());
    }
    let wrong = harness::compare(&mut s, &cases);
    assert!(wrong.is_empty(), "{}", wrong.iter().take(20).cloned().collect::<Vec<_>>().join("\n"));
}
