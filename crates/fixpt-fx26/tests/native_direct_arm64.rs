//! The native convention's compiler to arm64 written in FX-26
//! (`src/native-direct-arm64.fx` and the files beside it) against the Rust
//! one (`fixpt_native::direct`'s `procedure`), its oracle, piece by piece:
//! here the assembler and the sequences of no procedure
//! (`native-direct-arm64-asm.fx`), the same bytes and call-outs as the Rust
//! pieces of the same name (`fixpt_native::direct::oracle_arm64`). The
//! whole compiler, procedure by procedure, is `tests/native_x64.rs`'s
//! `compare_direct`. Any machine compiles for arm64; none runs the code
//! here.

#[path = "native-direct-arm64/harness.rs"]
mod harness;

use harness::{ints, Case, Wrapper, A};

const MODULES: &str = include_str!("native-direct-arm64/asm-modules.fx");

const WRAPPERS: &[Wrapper] = &[
    ("push-frame", &[("r", "int"), ("size", "int")], 0, "(ada-push-frame r size)"),
    ("pop-frame", &[("size", "int")], 0, "(ada-pop-frame size)"),
    ("leave", &[], 0, "(ada-leave)"),
    ("resume", &[], 0, "(ada-resume)"),
    ("call-out", &[("n", "int")], 0, "(ada-call-out n)"),
    ("ldr-field", &[("t", "int"), ("at", "int"), ("k", "int")], 0, "(begin (t-nops at) (ada-ldr-field t k))"),
    ("pure-call", &[("p", "int"), ("into", "int"), ("rs", "(listof int @k)")], 0, "(ada-pure-call (ada-co d-co-pure p (list-length rs)) rs into)"),
    ("check-fixnum", &[("r", "int")], 1, "(ada-check-fixnum r l0)"),
    ("card-mark", &[("obj", "int"), ("off", "int"), ("t1", "int"), ("t2", "int")], 0, "(ada-card-mark obj off t1 t2)"),
    ("imm", &[("r", "int"), ("hi", "int"), ("lo", "int")], 0, "(ada-imm r (+ (* hi 4294967296) lo))"),
    ("traps", &[("cs", "(listof int @k)")], 0, "(t-do-traps cs)"),
    ("branches", &[("n", "int"), ("fs", "(listof int @k)")], 0, "(t-do-branches n fs)"),
    ("unplaced", &[], 0, "(let ((l (ada-label))) (ada-b l))"),
];

/// Wrappers of their own shapes.
const EXTRA: &str = include_str!("native-direct-arm64/asm-extra.fx");

fn names() -> Vec<(&'static str, &'static str)> {
    let mut v: Vec<(&str, &str)> = [
        "ada-push-frame", "ada-pop-frame", "ada-leave", "ada-resume", "ada-call-out", "ada-ldr-field", "ada-pure-call", "ada-check-fixnum", "ada-card-mark", "ada-imm", "ada-trap", "ada-to",
        "ada-b", "ada-continuation-code",
    ]
    .iter()
    .map(|n| (*n, "asm"))
    .collect();
    v.push(("d-co-pure", "dl"));
    v
}

#[test]
fn the_assemblers_pieces_as_the_rust_compiler_makes_them() {
    let program = harness::program(MODULES, &names(), WRAPPERS, EXTRA);
    let mut s = harness::session(&program);
    let mut cases: Vec<Case> = Vec::new();
    let mut add = |name: &'static str, fx: Vec<A>, rust: Vec<i64>| cases.push((name, fx, rust));
    use A::{I, L};
    // A machine's own call-outs (`OWN_CALLOUTS`), which code alone can name:
    // another is loaded from a field of its code bloblet, which the
    // continuation procedure's code has not (`continuation_code`). A
    // call-out piece runs in `harness`, which gives each its field.
    for n in [0i64, 7, 9] {
        add("continuation-code", vec![I(n)], vec![n]);
    }
    for n in [0i64, 7, 9, 10, 37] {
        add("call-out", vec![I(n)], vec![n]);
    }
    for size in [16i64, 32, 208, 4096, 4112, 8192 + 48, 16368] {
        for r in [30i64, 17] {
            add("push-frame", vec![I(r), I(size)], vec![r, size]);
        }
        add("pop-frame", vec![I(size)], vec![size]);
    }
    add("leave", vec![], vec![]);
    add("resume", vec![], vec![]);
    for (t, at, k) in [(1i64, 0i64, 1i64), (16, 5, 3), (10, 100, 40), (16, 0, 131071), (16, 1, 131072), (16, 20, 131062), (16, 262_143, 1)] {
        add("ldr-field", vec![I(t), I(at), I(k)], vec![t, at, k]);
    }
    for (p, into, rs) in [(5i64, 0i64, vec![1i64, 2]), (300, 17, vec![0]), (12, 13, vec![13, 0, 9])] {
        let mut rust = vec![p, into];
        rust.extend(&rs);
        add("pure-call", vec![I(p), I(into), L(rs)], rust);
    }
    for r in [0i64, 1, 8, 16] {
        add("check-fixnum", vec![I(r)], vec![r]);
    }
    for (obj, off, t1, t2) in [(0i64, -12i64, 16i64, 17i64), (1, 4092, 13, 14), (17, 0, 16, 9)] {
        add("card-mark", vec![I(obj), I(off), I(t1), I(t2)], vec![obj, off, t1, t2]);
    }
    for (hi, lo) in [(0i64, 0i64), (0, 1), (0, 0xffff_ffff), (0x8000_0000, 0), (0xffff_ffff, 0xffff_fff8), (0x1234_5678, 0x9abc_def0), (0x7ff8_0000, 0)] {
        for r in [0i64, 16] {
            add("imm", vec![I(r), I(hi), I(lo)], vec![r, hi, lo]);
        }
    }
    add("traps", vec![L(vec![3, 1, 4, 1, 3, 0, 5, 11, 1, 3])], vec![3, 1, 4, 1, 3, 0, 5, 11, 1, 3]);
    add("traps", vec![L(vec![])], vec![]);
    // Each kind of branch, back and forth, to a `ret` and not, and out of
    // `b.cond`'s and `adr`'s reach.
    for fs in [
        vec![16i64, 0, 0, 16, 1, 2, 17, 0, 1, 1, 1, 0, 32 + 17, 2, 0, 11, 3, 4],
        vec![0, 1, 2, 16, 0, 1],
        vec![0, 1, 262_142, 16, 0, 1],
        vec![0, 1, 262_144, 16, 0, 1],
        vec![32 + 3, 0, 262_144],
    ] {
        let mut rust = vec![4];
        rust.extend(&fs);
        add("branches", vec![I(4), L(fs)], rust);
    }
    add("unplaced", vec![], vec![]);
    let _ = ints(&[]);
    let wrong = harness::compare(&mut s, &cases);
    assert!(wrong.is_empty(), "{}", wrong.iter().take(20).cloned().collect::<Vec<_>>().join("\n"));
}

/// The whole compiler's modules, applied as the conductor applies them:
/// that they check.
#[test]
fn the_compiler_checks() {
    if let Err(e) = fixpt_fx26::session::compile_program(include_str!("native-direct-arm64/compiler.fx")) {
        panic!("checks: {e}");
    }
}
