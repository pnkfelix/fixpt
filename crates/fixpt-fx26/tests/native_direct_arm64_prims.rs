//! The native convention's compiler to arm64 written in FX-26 against the
//! Rust one, piece by piece: here the fast paths of the primitives that
//! never collect and `string=?` (`native-direct-arm64-strings.fx`), the
//! same bytes and call-outs as the Rust pieces of the same name
//! (`fixpt_native::direct::oracle_arm64`, `pure_fast` and `string_eq`).
//! The arms that use them are the whole compiler's, procedure by
//! procedure (`tests/native_x64.rs`'s `compare_direct`).

#[path = "native-direct-arm64/harness.rs"]
mod harness;

use harness::{ints, Case, Wrapper, A};

const MODULES: &str = include_str!("native-direct-arm64/prims-modules.fx");

const WRAPPERS: &[Wrapper] = &[
    ("pure-fast", &[("y", "int"), ("name", "string")], 0, "(t-do-pure-fast y name)"),
    ("string-eq", &[("x", "int"), ("y", "int")], 0, "(adq-string-eq x y)"),
];

/// `pure-fast`'s answer before its code, its `slow` bound after it.
const EXTRA: &str = "
(define t-do-pure-fast (subr {EFF} (int string) (listof int @k))
  (lambda (y name)
    (let* ((slow (ada-label)) (fast (adq-pure-fast name y slow)))
      (t-out (cons (t-bit fast) nil) (cons slow nil)))))
";

#[test]
fn the_primitives_fast_paths_as_the_rust_compiler_makes_them() {
    let names: Vec<(&str, &str)> = vec![("adq-pure-fast", "strings"), ("adq-string-eq", "strings")];
    // `pure-fast`'s wrapper ends itself: its answer comes before its code.
    let program = harness::program(MODULES, &names, WRAPPERS, EXTRA).replace(
        "(begin (t-do-pure-fast y name) (t-out nil nil))",
        "(t-do-pure-fast y name)",
    );
    let mut s = harness::session(&program);
    let mut cases: Vec<Case> = Vec::new();
    let mut add = |name: &'static str, fx: Vec<A>, rust: Vec<i64>| cases.push((name, fx, rust));
    use A::{I, S};
    let mut known: Vec<&'static str> = vec![
        "null?", "pair?", "char?", "%fx26-f32?", "boolean?", "exact-integer?", "symbol?", "string?", "procedure?",
        "%fx26-mul", "%fx26-quotient", "modulo", "%fx26-remainder", "%fx26-arithmetic-shift", "%bloblet-fields",
        "bytevector-length", "bytevector-u8-ref", "string-length", "string-ref", "%fx26-flatarray-length",
        "%fx26-flatarray-ref", "%suffix-ref-offset", "%suffix-ref-owner", "%suffix-ref+",
        // None of these.
        "car", "", "%fx26-", "%fx26-i64+", "%fx26-u64-and", "%fx26-i8", "%fx26-i88+", "%fx26-i32+x", "%fx26-int->i64",
        "%fx26-int->", "%fx26-u3", "%fx26-f64+", "%fx26-f32", "%fx26-f32-bogus", "%fx26-i328+", "%fx26-u8u8",
        "%fx26-string<?", "char->integer",
    ];
    let ops = [
        "<", "<=", ">", ">=", "=", "->int", "+", "-", "*", "-quotient", "-remainder", "-and", "-or", "-xor", "-not", "-shl", "-shr", "-bogus", "",
    ];
    let mut owned: Vec<String> = Vec::new();
    for t in ["i8", "u8", "i32", "u32"] {
        owned.push(format!("%fx26-int->{t}"));
        for op in ops {
            owned.push(format!("%fx26-{t}{op}"));
        }
    }
    for op in ["<", "<=", ">", ">=", "=", "+", "-", "*", "/", "-abs", "-ceiling", "-floor", "-neg", "-round", "-sqrt", "-truncate", "-x"] {
        owned.push(format!("%fx26-f32{op}"));
    }
    known.extend(owned.into_iter().map(|n| &*Box::leak(n.into_boxed_str())));
    for name in &known {
        for y in [1i64, 2, 8, 17] {
            let mut rust = vec![y];
            rust.extend(ints(&[S(name)]));
            add("pure-fast", vec![I(y), S(name)], rust);
        }
    }
    for (x, y) in [(1i64, 2i64), (0, 17), (8, 3), (17, 1)] {
        add("string-eq", vec![I(x), I(y)], vec![x, y]);
    }
    let wrong = harness::compare(&mut s, &cases);
    assert!(wrong.is_empty(), "{}", wrong.iter().take(20).cloned().collect::<Vec<_>>().join("\n"));
}

/// The primitives' module (`native-direct-arm64-prims.fx`) checks, applied
/// as the conductor applies it (`native-direct-arm64/compiler.fx`); what it
/// does is the whole compiler's to show (`tests/native_x64.rs`).
#[test]
fn the_primitives_module_checks() {
    let program = include_str!("native-direct-arm64/prims-checks.fx");
    fixpt_fx26::session::compile_program(program).unwrap_or_else(|e| panic!("checks: {e}"));
}
