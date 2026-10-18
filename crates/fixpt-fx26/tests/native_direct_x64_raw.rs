//! The native convention's raw-value pieces written in FX-26
//! (`src/native-direct-x64-raw.fx`) against the Rust ones
//! (`fixpt_native::direct::oracle_x64`, `direct/x64/oracle_raw.rs`), piece
//! by piece: over every register each takes, every operation it tells
//! apart, both signednesses, every mask of raw parameters, and the shapes
//! of an `int` operation's slow path, the same bytes and the same
//! call-outs. Each piece runs in an assembler of its own; the labels it is
//! given are bound after it, in order, then its traps' stubs placed.

use fixpt_engine::Backend;
use fixpt_heap::Value;

/// An argument to a piece: FX-26 is given it as itself, the Rust oracle
/// as integers (a name as its bytes, last).
#[derive(Clone, Debug)]
enum A {
    I(i64),
    B(bool),
    S(&'static str),
    L(Vec<i64>),
}

const EFF: &str = "(maxeff (read @globals) (read @k) (write @k) (alloc @k) spin)";

/// Each piece's FX-26 wrapper: its name, its parameters' types, the labels
/// it is given, and the call.
type Wrapper = (&'static str, &'static [(&'static str, &'static str)], usize, &'static str);
const WRAPPERS: &[Wrapper] = &[
    ("box-reg", &[("r", "int"), ("s", "bool")], 0, "(dr-box-reg r s)"),
    ("unbox-reg", &[("r", "int")], 0, "(dr-unbox-reg r)"),
    ("unbox-f64", &[("r", "int")], 0, "(dr-unbox-f64 r)"),
    ("raw-entry", &[("p", "int")], 0, "(dr-raw-entry p)"),
    ("take-raw-f64", &[], 0, "(dr-take-raw-f64)"),
    ("raw-return", &[], 0, "(dr-raw-return)"),
    ("box-f64", &[("r", "int")], 0, "(dr-box-f64 r)"),
    ("box-bits", &[], 1, "(dr-box-bits l0)"),
    ("unbox-to", &[("r", "int"), ("rep", "int")], 0, "(dr-unbox-to r rep)"),
    ("convert", &[("res", "int"), ("cs", "(listof int @k)")], 1, "(dr-convert cs l0 res)"),
    ("f64-of-int", &[("p", "int")], 0, "(dr-f64-of-int p)"),
    ("int-of-f64", &[("p", "int")], 0, "(dr-int-of-f64 p)"),
    ("f64-fast", &[("y", "int"), ("w", "string")], 0, "(dr-f64-fast w y)"),
    ("wrap-small", &[("s", "bool"), ("bits", "int")], 0, "(dr-wrap-small s bits)"),
    ("raw-fast", &[("s", "bool"), ("y", "int"), ("w", "string")], 0, "(dr-raw-fast s w y)"),
];

/// The FX-26 program: the modules, as the conductor makes them; what the
/// wrappers use of them; and the wrappers.
fn program() -> String {
    let mut p = String::from(include_str!("native-direct/raw-modules.fx"));
    for n in ["da-reset", "da-label", "da-bind", "da-e", "da-place-stubs", "da-finish", "da-callouts"] {
        p.push_str(&format!("(define {n} (with asm {n}))\n"));
    }
    for n in [
        "dr-box-reg", "dr-unbox-reg", "dr-unbox-f64", "dr-raw-entry", "dr-raw-entry-skip", "dr-take-raw-f64", "dr-raw-return", "dr-box-f64",
        "dr-box-bits", "dr-unbox-to", "dr-convert", "dr-f64-of-int", "dr-int-of-f64", "dr-float-test", "dr-f64-fast", "dr-f32-fast",
        "dr-wrap-small", "dr-raw-fast", "dr-narrow-fast", "dr-int-slow",
    ] {
        p.push_str(&format!("(define {n} (with raw {n}))\n"));
    }
    // The labels `ls` bound, the stubs placed: the call-outs' count, the
    // call-outs, `pre`, and the bytes.
    p.push_str(&include_str!("native-direct/raw-out.fx").replace("{EFF}", EFF));
    let labels = |n: usize| (0..n).map(|k| format!("(l{k} (da-label))")).collect::<Vec<_>>().join(" ");
    let list = |n: usize| (0..n).rev().fold("nil".to_string(), |acc, k| format!("(cons l{k} {acc})"));
    for (name, params, n, call) in WRAPPERS {
        let types = params.iter().map(|p| p.1).collect::<Vec<_>>().join(" ");
        let names = params.iter().map(|p| p.0).collect::<Vec<_>>().join(" ");
        p.push_str(&format!(
            "(define t-{name} (subr {EFF} ({types}) (listof int @k))\n  \
               (lambda ({names}) (begin (da-reset 0) (let* ({ls}) (begin {call} (t-out nil {l}))))))\n",
            ls = if *n == 0 { "(l- 0)".to_string() } else { labels(*n) },
            l = list(*n),
        ));
    }
    // Those that answer whether they did something, and those of their
    // own shapes.
    p.push_str(&include_str!("native-direct/raw-shapes.fx").replace("{EFF}", EFF));
    p
}

/// The Rust oracle's integers for `args`.
fn ints(args: &[A]) -> Vec<i64> {
    let mut out = Vec::new();
    for a in args {
        match *a {
            A::I(n) => out.push(n),
            A::B(b) => out.push(b as i64),
            A::S(s) => out.extend(s.bytes().map(i64::from)),
            A::L(ref l) => out.extend(l),
        }
    }
    out
}

#[test]
fn every_raw_value_piece_as_the_rust_compiler_makes_it() {
    let program = program();
    let compiled = fixpt_fx26::session::compile_program(&program).unwrap_or_else(|e| panic!("checks: {e}\n{program}"));
    let mut s = fixpt_scheme::Session::with_backend(Backend::Bytecode);
    compiled.load_into(&mut s).expect("loads");

    let mut cases: Vec<(&str, Vec<A>, Vec<i64>)> = Vec::new();
    let mut add = |name: &'static str, fx: Vec<A>, rust: Vec<i64>| cases.push((name, fx, rust));
    use A::{B, I, S};
    let all: Vec<i64> = (0..16).collect();
    let regs: Vec<i64> = (0..=8).collect();
    for &r in &all {
        for sg in [false, true] {
            add("box-reg", vec![I(r), B(sg)], ints(&[I(r), B(sg)]));
        }
        add("unbox-reg", vec![I(r)], vec![r]);
        add("unbox-f64", vec![I(r)], vec![r]);
        add("box-f64", vec![I(r)], vec![r]);
    }
    for p in 0..256 {
        add("raw-entry", vec![I(p)], vec![p]);
        add("raw-entry-skip", vec![I(p)], vec![p]);
    }
    add("take-raw-f64", vec![], vec![]);
    add("raw-return", vec![], vec![]);
    add("box-bits", vec![], vec![]);
    for &r in &regs {
        for rep in 0..=5 {
            add("unbox-to", vec![I(r), I(rep)], vec![r, rep]);
            for kind in 0..=2 {
                for res in [0i64, 1, 13] {
                    let c = 128 * kind + 8 * r + rep;
                    add("convert", vec![I(res), A::L(vec![c])], vec![res, c]);
                }
            }
        }
    }
    for cs in [vec![0 * 128 + 8 + 4, 128 + 16 + 2, 256 + 24 + 5], vec![256, 128 + 64 + 4, 2 * 8 + 3, 256 + 8 * 8 + 5]] {
        let mut rust = vec![14];
        rust.extend(&cs);
        add("convert", vec![I(14), A::L(cs)], rust);
    }
    for p in [0i64, 77, 400] {
        add("f64-of-int", vec![I(p)], vec![p]);
        add("int-of-f64", vec![I(p)], vec![p]);
    }
    let floats = ["+", "-", "*", "/", "-abs", "-neg", "-sqrt", "-floor", "-ceiling", "-truncate", "-round", "<", "<=", ">", ">=", "=", "-min", "-exp"];
    for w in floats {
        for d in [false, true] {
            add("float-test", vec![B(d), S(w)], ints(&[B(d), S(w)]));
        }
        for &y in &all {
            if !matches!(w, "-min" | "-exp") {
                add("f64-fast", vec![I(y), S(w)], ints(&[I(y), S(w)]));
            }
            add("f32-fast", vec![I(y), S(w)], ints(&[I(y), S(w)]));
        }
    }
    for sg in [false, true] {
        for bits in [8, 32] {
            add("wrap-small", vec![B(sg), I(bits)], ints(&[B(sg), I(bits)]));
        }
        for w in ["from", "+", "-", "*", "-and", "-or", "-xor", "-not", "-quotient", "-remainder", "-shl", "-shr", "<", "<=", ">", ">=", "="] {
            for y in (3..16).filter(|&y| y != 4) {
                add("raw-fast", vec![B(sg), I(y), S(w)], ints(&[B(sg), I(y), S(w)]));
            }
        }
    }
    let ops = ["->int", "+", "-", "*", "-quotient", "-remainder", "-and", "-or", "-xor", "-not", "-shl", "-shr", "<", "<=", ">", ">=", "=", "-min"];
    let mut names: Vec<String> = Vec::new();
    for t in ["i8", "u8", "i32", "u32"] {
        for op in ops {
            names.push(format!("%fx26-{t}{op}"));
        }
        names.push(format!("%fx26-int->{t}"));
    }
    for w in floats {
        names.push(format!("%fx26-f32{w}"));
    }
    names.extend(["%fx26-i64+", "%fx26-u8x", "foo", "%fx26-int->i64", "%fx26-i328+", "%fx26-u3"].map(String::from));
    let names: Vec<&'static str> = names.into_iter().map(|n| &*Box::leak(n.into_boxed_str())).collect();
    for &n in &names {
        for y in [3i64, 7, 14, 9] {
            add("narrow-fast", vec![I(y), S(n)], ints(&[I(y), S(n)]));
        }
    }
    let mut slows = 0;
    for ov in [false, true] {
        for x in [0i64, 1, 7] {
            for (y, imm) in [(-1i64, 5i64), (-1, -8), (-1, 1000), (9, 0), (6, 0)] {
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

    let mut wrong = Vec::new();
    let mut per: std::collections::BTreeMap<&str, usize> = Default::default();
    for (name, fx, rust) in &cases {
        *per.entry(name).or_default() += 1;
        let (want_code, want_calls) = fixpt_native::direct::oracle_x64(name, rust).unwrap_or_else(|| panic!("no Rust piece {name}"));
        let got: Vec<i64> = s.scope(|sc| {
            let args: Vec<_> = fx
                .iter()
                .map(|a| match *a {
                    A::I(n) => sc.make(|_| Value::fixnum(n)),
                    A::B(b) => sc.make(|_| Value::boolean(b)),
                    A::S(t) => sc.make(|m| m.heap().make_string(t)),
                    A::L(ref l) => sc.make(|m| l.iter().rev().fold(Value::NULL, |acc, &n| m.heap().cons(Value::fixnum(n), acc))),
                })
                .collect();
            let r = sc.call_global(&format!("fx:t-{name}"), &args).unwrap_or_else(|e| panic!("{name} {fx:?} runs: {e}"));
            sc.view(|v| v.get(r).list().expect("a list").iter().map(|b| b.fixnum().expect("an int")).collect())
        });
        let k = got[0] as usize;
        let (calls, code): (Vec<i64>, Vec<u8>) = (got[1..1 + k].to_vec(), got[1 + k..].iter().map(|&b| b as u8).collect());
        if code != want_code || calls != want_calls {
            wrong.push(format!("{name} {fx:?}: FX-26 {code:02x?} {calls:?}, Rust {want_code:02x?} {want_calls:?}"));
        }
    }
    eprintln!("{} pieces compared ({slows} slow paths): {per:?}; {} differ", cases.len(), wrong.len());
    assert!(wrong.is_empty(), "{}", wrong.iter().take(20).cloned().collect::<Vec<_>>().join("\n"));
}
