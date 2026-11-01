//! The native convention's raw-value pieces for arm64 written in FX-26
//! (`src/native-direct-arm64-raw.fx`) against the Rust ones
//! (`fixpt_native::direct::oracle_arm64`, `direct/fx_arm64/oracle_raw.rs`),
//! piece by piece: over every register each takes, every operation it
//! tells apart (and some it does not know), both signednesses, every
//! conversion, and the shapes of an `int` operation's slow path, the same
//! bytes and the same call-outs. Each piece runs in an assembler of its
//! own (`native-direct-arm64/harness.rs`).

#[path = "native-direct-arm64/harness.rs"]
mod harness;

use harness::{ints, Case, Wrapper, A};

const MODULES: &str = include_str!("native-direct-arm64/raw-modules.fx");

const WRAPPERS: &[Wrapper] = &[
    ("box-reg", &[("r", "int"), ("s", "bool")], 0, "(adr-box-reg r s)"),
    ("unbox-reg", &[("r", "int")], 0, "(adr-unbox-reg r)"),
    ("unbox-f64", &[("r", "int")], 0, "(adr-unbox-f64 r)"),
    ("raw-f64-mark", &[], 0, "(ada-e adr-raw-f64-mark)"),
    ("take-raw-f64", &[], 0, "(adr-take-raw-f64)"),
    ("raw-return", &[], 0, "(adr-raw-return)"),
    ("box-f64", &[("r", "int")], 0, "(adr-box-f64 r)"),
    ("unbox-to", &[("r", "int"), ("rep", "int")], 0, "(adr-unbox-to r rep)"),
    ("convert", &[("res", "int"), ("cs", "(listof int @k)")], 1, "(adr-convert cs l0 res)"),
    ("f64-of-int", &[("p", "int")], 0, "(adr-f64-of-int p)"),
    ("int-of-f64", &[("p", "int")], 0, "(adr-int-of-f64 p)"),
    ("f64-fast", &[("y", "int"), ("w", "string")], 0, "(adr-f64-fast w y)"),
    ("raw-fast", &[("s", "bool"), ("y", "int"), ("w", "string")], 0, "(adr-raw-fast s w y)"),
    ("wrap-small", &[("s", "bool"), ("bits", "int")], 0, "(adr-wrap-small s bits)"),
];

fn names() -> Vec<(&'static str, &'static str)> {
    [
        "adr-box-reg", "adr-unbox-reg", "adr-unbox-f64", "adr-raw-f64-mark", "adr-take-raw-f64", "adr-raw-return", "adr-raw-entry-skip", "adr-box-f64", "adr-unbox-to",
        "adr-convert", "adr-f64-of-int", "adr-int-of-f64", "adr-f64-fast", "adr-f32-fast", "adr-compare", "adr-raw-fast", "adr-wrap-small", "adr-int-slow",
    ]
    .iter()
    .map(|n| (*n, "raw"))
    .collect()
}

#[test]
fn every_raw_value_piece_as_the_rust_compiler_makes_it() {
    let program = harness::program(MODULES, &names(), WRAPPERS, include_str!("native-direct-arm64/raw-shapes.fx"));
    let mut s = harness::session(&program);
    let mut cases: Vec<Case> = Vec::new();
    let mut add = |name: &'static str, fx: Vec<A>, rust: Vec<i64>| cases.push((name, fx, rust));
    use A::{B, I, L, S};
    let all: Vec<i64> = (0..16).collect();
    for &r in &all {
        for sg in [false, true] {
            add("box-reg", vec![I(r), B(sg)], ints(&[I(r), B(sg)]));
        }
        add("unbox-reg", vec![I(r)], vec![r]);
        add("unbox-f64", vec![I(r)], vec![r]);
        add("box-f64", vec![I(r)], vec![r]);
    }
    add("raw-f64-mark", vec![], vec![]);
    add("take-raw-f64", vec![], vec![]);
    add("raw-return", vec![], vec![]);
    for n in 0..=16 {
        add("raw-entry-skip", vec![I(n)], vec![n]);
    }
    for &r in &all {
        for rep in 0..=5 {
            add("unbox-to", vec![I(r), I(rep)], vec![r, rep]);
            for kind in 0..=2 {
                for res in [0i64, 1, 13] {
                    let c = 128 * kind + 8 * r + rep;
                    add("convert", vec![I(res), L(vec![c])], vec![res, c]);
                }
            }
        }
    }
    for cs in [vec![], vec![8 + 4, 128 + 16 + 2, 256 + 24 + 5], vec![256, 128 + 64 + 4, 2 * 8 + 3, 256 + 8 * 8 + 5, 15 * 8 + 2, 128 + 15 * 8 + 3]] {
        let mut rust = vec![14];
        rust.extend(&cs);
        add("convert", vec![I(14), L(cs)], rust);
    }
    for p in [0i64, 77, 400] {
        add("f64-of-int", vec![I(p)], vec![p]);
        add("int-of-f64", vec![I(p)], vec![p]);
    }
    let floats = ["+", "-", "*", "/", "-abs", "-neg", "-sqrt", "-floor", "-ceiling", "-truncate", "-round", "<", "<=", ">", ">=", "=", "-min", "-exp", "->f64"];
    for w in floats {
        for &y in &all {
            add("f64-fast", vec![I(y), S(w)], ints(&[I(y), S(w)]));
            add("f32-fast", vec![I(y), S(w)], ints(&[I(y), S(w)]));
        }
    }
    let raws = ["from", "+", "-", "*", "-and", "-or", "-xor", "-not", "-quotient", "-remainder", "-shl", "-shr", "<", "<=", ">", ">=", "="];
    for sg in [false, true] {
        for bits in [8, 32] {
            add("wrap-small", vec![B(sg), I(bits)], ints(&[B(sg), I(bits)]));
        }
        for w in raws.iter().chain(&["->int", "-min", "foo", ""]) {
            add("compare", vec![B(sg), S(w)], ints(&[B(sg), S(w)]));
        }
        for w in raws {
            for &y in &all {
                add("raw-fast", vec![B(sg), I(y), S(w)], ints(&[B(sg), I(y), S(w)]));
            }
        }
    }
    let mut slows = 0;
    for ov in [false, true] {
        for x in [0i64, 1, 7] {
            for (y, imm) in [(-1i64, 5i64), (-1, 1000), (-1, 4095), (9, 0), (6, 0)] {
                for into in [0i64, x, 14] {
                    for sub in [false, true] {
                        for (br, when) in [(false, false), (true, false), (true, true)] {
                            for prim in [10i64, 300] {
                                let a = [B(ov), I(x), I(y), I(imm), I(into), I(prim), B(sub), B(br), B(when)];
                                add("int-slow", a.to_vec(), ints(&a));
                                slows += 1;
                            }
                        }
                    }
                }
            }
        }
    }
    eprintln!("{slows} slow paths");
    let wrong = harness::compare(&mut s, &cases);
    assert!(wrong.is_empty(), "{}", wrong.iter().take(20).cloned().collect::<Vec<_>>().join("\n"));
}
