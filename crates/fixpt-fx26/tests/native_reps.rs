//! Where native code keeps raw values, by the pass written in FX-26
//! (`src/native-reps.fx`) against the Rust one (`fixpt_native::direct`'s
//! `reps.rs`), its oracle (`fixpt_native::direct::reps_oracle`): for every
//! register word of the front end compiled with register code, the cells
//! split, where instructions start, the raw slots and parameters, the raw
//! references, what is live, the frame's webs, and in each version (fixnum
//! and general, with and without callees known) every instruction's
//! representations and the conversions before it, the same. And the pieces of no word: joins,
//! unboxings, checks, and every primitive's raw operation.

mod common;

use fixpt_engine::Backend;
use fixpt_heap::layout::cellular::{CLOSURE_WORD, WORD_CELL0, WORD_TWIN};
use fixpt_heap::layout::kind;
use fixpt_heap::{Heap, Value};
use fixpt_native::direct::reps_oracle as oracle;
use fixpt_read::FileId;
use fixpt_scheme::Handle;

/// The pass's modules, and what the test calls of them: each step on a
/// register word, given as its `tword`, its results as lists of ints.
const PROGRAM: &str = include_str!("native-direct/reps.fx");

/// Every register word `word` reaches through its cells and operands, by
/// the cellular words that have them.
fn twins(heap: &Heap, word: Value) -> Vec<Value> {
    let closure = kind("cellular-closure");
    let (mut todo, mut seen, mut out) = (vec![word], std::collections::HashSet::new(), Vec::new());
    while let Some(w) = todo.pop() {
        if !seen.insert(w.raw()) {
            continue;
        }
        let t = heap.bloblet_slot(w, WORD_TWIN);
        if heap.is_register_word(t) {
            out.push(t);
        }
        for k in WORD_CELL0..=heap.bloblet_head(w).fields {
            let v = heap.bloblet_slot(w, k);
            if heap.is_cellular_word(v) {
                todo.push(v);
            } else if v.is_bloblet() && heap.bloblet_kind(v) == closure {
                todo.push(heap.bloblet_slot(v, CLOSURE_WORD));
            }
        }
    }
    out
}

/// FX-26's `name` on `args` (a register word, then ints): a list of ints.
fn ints(sc: &mut fixpt_scheme::Session, name: &str, rw: Handle, args: &[i64]) -> Vec<i64> {
    sc.scope(|one| {
        let mut all = vec![rw];
        all.extend(args.iter().map(|&x| one.make(|_| Value::fixnum(x))));
        let r = one.call_global(&format!("fx:{name}"), &all).unwrap_or_else(|e| panic!("{name} runs: {e}"));
        one.view(|v| {
            let r = v.get(r);
            match r.fixnum() {
                Some(n) => vec![n],
                None => r.list().expect("a list").iter().map(|x| x.fixnum().expect("an int")).collect(),
            }
        })
    })
}

fn bits(v: &[bool]) -> Vec<i64> {
    v.iter().map(|&b| b as i64).collect()
}

/// The pass on `limit` register words of the front end, or all of them.
fn compare(limit: usize) {
    let mut s = common::front_end_session();
    // The pass as register code too: lowered, some words took minutes.
    s.program_as_register_code(PROGRAM, &["t-all"], "fx").unwrap_or_else(|e| panic!("compiles: {e}"));
    let text = fixpt_fx26::bootstrap_program();
    let (mut wrong, mut compared, mut instructions, mut split) = (Vec::new(), 0, 0, 0);
    s.scheme.scope(|sc| {
        let facts = fixpt_fx26::syn::rust_facts(sc, FileId(0), &text).expect("checks");
        let stage1 = fixpt_fx26::syn::compile_to_word_with_registers(sc, FileId(0), &text, facts).expect("parses").expect("compiles");
        let mut found = Vec::new();
        sc.make(|m| {
            let w = m.get(stage1);
            found = twins(m.heap(), w);
            Value::NULL
        });
        let rws: Vec<Handle> = found.into_iter().take(limit).map(|w| sc.make(|_| w)).collect();
        let mut progress = common::Progress::new("register words compared", rws.len());
        for rw in rws {
            progress.at(compared);
            let mut f = None;
            let mut raw_cells = Vec::new();
            sc.make(|m| {
                let v = m.get(rw);
                let heap = m.heap();
                raw_cells = (WORD_CELL0..=heap.bloblet_head(v).fields).map(|k| heap.bloblet_slot(v, k)).collect();
                f = Some(oracle::facts(heap, v));
                Value::NULL
            });
            let f = f.expect("facts");
            compared += 1;
            instructions += f.starts.len();
            if raw_cells.iter().zip(&f.cells).any(|(a, b)| a.is_fixnum() && a.as_fixnum() != *b) {
                split += 1;
            }
            // The parts as `t-all` gives them, each ended by -1000000007; the
            // versions in its order (`facts`'s too).
            let mut parts: Vec<(String, Vec<i64>)> = vec![
                ("split cells".into(), f.cells.clone()),
                ("starts".into(), f.starts.iter().map(|&x| x as i64).collect()),
                ("raw slots".into(), bits(&f.raw)),
                ("raw params".into(), vec![f.params]),
                ("raw refs".into(), bits(&f.raw_refs)),
                ("live".into(), f.live.clone()),
                ("webs".into(), f.webs.clone()),
            ];
            for v in &f.versions {
                let known = v.callees.iter().any(|&c| c != 0);
                let mut want = v.ins.clone();
                want.extend(&v.outs);
                for st in &v.steps {
                    want.extend(st);
                    want.push(-1);
                }
                parts.push((format!("reps, fast {} callees known {known}", v.fast), want));
            }
            let got = ints(sc, "t-all", rw, &[f.slots]);
            let got: Vec<&[i64]> = got.split(|&x| x == -1000000007).collect();
            for (k, (what, want)) in parts.iter().enumerate() {
                if got.get(k).copied() != Some(&want[..]) {
                    wrong.push(format!("word {compared}, {what}: FX-26 {:?}, Rust {want:?}", got.get(k)));
                }
            }
        }
    });
    eprintln!("{compared} register words, {instructions} instructions, {split} with slots split; {} differ", wrong.len());
    assert!(compared > 0, "no register words");
    assert!(wrong.is_empty(), "{}", wrong.iter().take(10).cloned().collect::<Vec<_>>().join("\n"));
}

#[test]
fn some_register_words_as_the_rust_pass_finds_them() {
    compare(60);
}

#[test]
#[cfg_attr(not(optimized), ignore = "every register word of the front end: run with --release")]
fn every_register_word_of_the_front_end_as_the_rust_pass_finds_it() {
    compare(usize::MAX);
}

/// A program of the pieces alone, in a session of its own.
fn pieces() -> fixpt_scheme::Session {
    let compiled = fixpt_fx26::session::compile_program(PROGRAM).unwrap_or_else(|e| panic!("checks: {e}"));
    let mut s = fixpt_scheme::Session::with_backend(Backend::Bytecode);
    compiled.load_into(&mut s).expect("loads");
    s
}

fn call_ints(s: &mut fixpt_scheme::Session, name: &str, args: &[i64]) -> Vec<i64> {
    s.scope(|sc| {
        let args: Vec<_> = args.iter().map(|&x| sc.make(|_| Value::fixnum(x))).collect();
        let r = sc.call_global(&format!("fx:{name}"), &args).unwrap_or_else(|e| panic!("{name} runs: {e}"));
        sc.view(|v| {
            let r = v.get(r);
            match r.fixnum() {
                Some(n) => vec![n],
                None => r.list().expect("a list").iter().map(|x| x.fixnum().expect("an int")).collect(),
            }
        })
    })
}

/// Joins, unboxings and checks over every pair of each register's
/// representations, packed, and with other registers' around them.
#[test]
fn joins_unboxings_and_checks_as_the_rust_pass_makes_them() {
    let mut s = pieces();
    let mut cases = 0;
    for a in 0..6i64 {
        for b in 0..6i64 {
            for r in [0, 4, 8] {
                let (pa, pb) = ((a << (3 * r)) | 1 << (3 * ((r + 1) % 9)), (b << (3 * r)) | 4 << (3 * ((r + 2) % 9)));
                assert_eq!(call_ints(&mut s, "nr-join", &[pa, pb]), vec![oracle::join(pa, pb)], "join {a} {b} at {r}");
                assert_eq!(call_ints(&mut s, "nr-unboxes", &[pa, pb]), oracle::unboxes(pa, pb), "unboxes {a} {b} at {r}");
                for live in [0, 0x1ff, 1 << r] {
                    assert_eq!(call_ints(&mut s, "nr-checks", &[pa, pb, live]), oracle::checks(pa, pb, live), "checks {a} {b} at {r}");
                }
                cases += 1;
            }
        }
    }
    eprintln!("{cases} pairs agree");
}

/// Every primitive's raw operation, as `raw_op` reads its name.
#[test]
fn every_primitives_raw_operation_as_the_rust_pass_reads_it() {
    let mut s = pieces();
    for d in fixpt_runtime::PRIMITIVES.iter() {
        let (kind, signed, what) = oracle::raw_op(d.name);
        let want = format!("{kind} {} {what}", if signed { "#t" } else { "#f" });
        let got = s.scope(|sc| {
            let n = sc.make(|m| m.heap().make_string(d.name));
            let r = sc.call_global("fx:t-raw-op", &[n]).expect("runs");
            sc.view(|v| v.get(r).string().expect("a string"))
        });
        assert_eq!(got, want, "{}", d.name);
    }
}

/// `reps.rs`'s own case: a slot that holds an `f64`, then an `int`, split,
/// its `f64` web moved to a slot of its own, kept raw.
#[test]
fn a_slot_of_an_f64_and_an_int_is_split() {
    use fixpt_heap::layout::regcode::op;
    let add = fixpt_runtime::PRIMITIVES.iter().position(|d| d.name == "%fx26-f64+").expect("f64+") as i64;
    let c = |name: &str, args: &[i64]| -> Vec<i64> { std::iter::once(op(name) as i64).chain(args.iter().copied()).collect() };
    let cells: Vec<i64> = [
        c("args", &[1]),
        c("save", &[1]),
        c("reg", &[1]),
        c("prim2", &[add, 1]),
        c("setstk", &[0]),
        c("stack", &[0]),
        c("prim2", &[add, 1]),
        c("setreg", &[1]),
        c("const", &[5]),
        c("setstk", &[0]),
        c("stack", &[0]),
        c("pop", &[1]),
        c("return", &[]),
    ]
    .concat();
    let list = cells.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(" ");
    let program = format!(
        "{PROGRAM}\n(define t-case (subr t-does () t-list)\n  (lambda ()\n    (let* ((l (the t-list (list {list})))\n           (n (t-count l))\n           (fix (t-array l n))\n           (is (the t-bools (make-array n #t)))\n           (c (nr-split-slots (tup (1 fix) (2 is))))\n           (s (nr-starts c)))\n      (append (t-ints (extract c 1)) (t-bools (nr-raw-slots c s 2))))))\n"
    );
    let compiled = fixpt_fx26::session::compile_program(&program).unwrap_or_else(|e| panic!("checks: {e}"));
    let mut s = fixpt_scheme::Session::with_backend(Backend::Bytecode);
    compiled.load_into(&mut s).expect("loads");
    let got = call_ints(&mut s, "t-case", &[]);
    let (split, raw) = got.split_at(cells.len());
    let mut starts = Vec::new();
    let mut i = 0;
    while i < split.len() {
        starts.push(i);
        i += 1 + fixpt_heap::layout::regcode::OPS[split[i] as usize].1;
    }
    let operand = |k: usize| split[starts[k] + 1];
    assert_eq!((operand(1), operand(4), operand(5), operand(9), operand(10), operand(11)), (2, 1, 1, 0, 0, 2));
    assert_eq!(raw, [0, 1]);
}
