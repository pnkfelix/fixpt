//! The heap's fast paths of the native convention's compiler to x86_64
//! written in FX-26 (`src/native-direct-x64-flat.fx`) against the Rust
//! ones (`fixpt_native::direct::oracle_x64`), piece by piece: the same
//! bytes, over every register a piece may be given, every layout, and
//! every shape predicate. Any machine compiles for x86_64; none runs the
//! code here.

use fixpt_engine::Backend;
use fixpt_heap::Value;

/// The shape predicates, by the index both sides name them by
/// (`oracle_flat::SHAPES`).
const SHAPES: [&str; 14] = [
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

/// A raw values' module that does only what these pieces need of it,
/// `box_bits` (`direct/x64.rs`'s, as `native-direct-x64-raw.fx` is to do it).
const RAW_STAND_IN: &str = include_str!("native-direct/flat-raw-stand-in.fx");

/// Each piece as the oracle runs it: the assembler reset, `slow` and the
/// other label (`done` or `wide`) made, the piece, both bound, an `int3`,
/// the bytes.
const WRAPPERS: &str = include_str!("native-direct/flat-wrappers.fx");

/// The pieces, `t-` and the oracle's name.
const PIECES: [&str; 20] = [
    "flat-count",
    "flat-element",
    "flat-ref",
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
    "wide-layout",
    "suffix-set",
    "bytes-set",
    "flat-set",
    "shape-fast",
];

fn session() -> fixpt_scheme::Session {
    let mut program = String::from(include_str!("native-direct/flat-modules.fx"));
    program.push_str(RAW_STAND_IN);
    program.push_str("(define flat ((load-input \"fx26:native-direct-x64-flat.fx\") x86-64 dl asm raw))\n");
    program.push_str(WRAPPERS);
    for p in PIECES {
        program.push_str(&format!("(define t-{p} (with tests t-{p}))\n"));
    }
    let compiled = fixpt_fx26::session::compile_program(&program).unwrap_or_else(|e| panic!("checks: {e}"));
    let mut s = fixpt_scheme::Session::with_backend(Backend::Bytecode);
    compiled.load_into(&mut s).expect("loads");
    s
}

/// What FX-26's piece makes of integer `args`.
fn ints_of(s: &mut fixpt_scheme::Session, name: &str, args: &[i64]) -> Vec<i64> {
    s.scope(|sc| {
        let args: Vec<_> = args.iter().map(|x| sc.make(|_| Value::fixnum(*x))).collect();
        let r = sc.call_global(&format!("fx:t-{name}"), &args).unwrap_or_else(|e| panic!("{name} runs: {e}"));
        sc.view(|v| v.get(r).list().expect("a list").iter().map(|b| b.fixnum().expect("an int")).collect())
    })
}

/// The flat layouts, the scalars' codes.
const LAYOUTS: [i64; 6] = [0, 1, 2, 3, 4, 5];

/// Array operands (`layout::array_operand`): lengths, the last running to
/// the end, by element sizes, powers of two and not.
fn array_operands() -> Vec<i64> {
    let mut out = Vec::new();
    for n in [0i64, 1, 3, 1000, fixpt_heap::layout::FLAT_TO_THE_END] {
        for size in [1i64, 2, 4, 8, 12, 24, 3] {
            out.push((n << fixpt_heap::layout::ARRAY_OPERAND_LENGTH_SHIFT) | size);
        }
    }
    out
}

/// Flat sums' codes: a tag's width (1, 2 or 4 bytes), numeric or not, and
/// where the payload is.
fn sum_codes() -> Vec<i64> {
    let mut out = Vec::new();
    for w in [1i64, 2, 4] {
        for numeric in [0i64, 8] {
            for p in [0i64, 3, 200, 4096] {
                out.push(w | numeric | p << 8);
            }
        }
    }
    out
}

#[test]
fn every_heap_piece_as_the_rust_compiler_makes_it() {
    let mut s = session();
    let regs: Vec<i64> = (0..16).collect();
    let mut cases: Vec<(&str, Vec<i64>)> = Vec::new();
    for &x in &regs {
        for &y in &regs {
            cases.push(("flat-count", vec![x, y]));
            cases.push(("flat-element", vec![x, y]));
        }
        cases.push(("flat-ref", vec![x]));
        cases.push(("suffix-owner", vec![x]));
        cases.push(("suffix-writable", vec![x]));
        cases.push(("wide-layout", vec![x]));
        for code in LAYOUTS {
            for raw in [0, 1] {
                cases.push(("suffix-store", vec![code, x, raw]));
            }
        }
        for code in array_operands() {
            cases.push(("blobref-index", vec![code, x]));
        }
        for code in sum_codes() {
            cases.push(("flat-variant", vec![code, x]));
        }
    }
    for d in [0i64, 1, 8, 1000, (1 << 24) - 1, (1 << 26) - 1] {
        cases.push(("blobref-at", vec![d]));
        cases.push(("suffix-step", vec![d]));
        cases.push(("suffix-fits", vec![d]));
    }
    for code in array_operands() {
        cases.push(("suffix-length", vec![code]));
    }
    for code in sum_codes() {
        cases.push(("flat-tag", vec![code]));
    }
    for code in LAYOUTS {
        for raw in [0, 1] {
            cases.push(("suffix-get", vec![code, raw]));
        }
    }
    cases.push(("suffix-index", vec![]));
    cases.push(("suffix-set", vec![]));
    cases.push(("bytes-set", vec![]));
    for raw in [0, 1] {
        cases.push(("flat-set", vec![raw]));
    }
    for k in 0..SHAPES.len() as i64 {
        cases.push(("shape-fast", vec![k]));
    }
    let mut wrong = Vec::new();
    let mut bytes = 0;
    for (name, args) in &cases {
        let (code, known) = fixpt_native::direct::oracle_x64(name, args).unwrap_or_else(|| panic!("no Rust piece {name}"));
        let mut want: Vec<i64> = code.iter().map(|&b| b as i64).collect();
        if *name == "shape-fast" {
            want.extend(known);
        }
        let got = ints_of(&mut s, name, args);
        bytes += want.len();
        if got != want {
            wrong.push(format!("{name} {args:?}: FX-26 {got:02x?}, Rust {want:02x?}"));
        }
    }
    eprintln!("{} heap pieces, {bytes} bytes; {} differ", cases.len(), wrong.len());
    assert!(wrong.is_empty(), "{}", wrong.iter().take(20).cloned().collect::<Vec<_>>().join("\n"));
}
