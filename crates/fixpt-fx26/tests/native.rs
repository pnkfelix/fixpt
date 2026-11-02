//! Words compiled to machine code by the compiler written in FX-26
//! (`src/native.fx`) against the Rust one (`fixpt_native::cellular::
//! assemble_word`), its oracle: for every word of the bootstrap program,
//! compiled, the same instructions and the same places where each cell's
//! code starts (`PLAN.md` §11, 11c).

mod common;

use fixpt_fx26::session::READER_PREFIX;
use fixpt_heap::layout::kind;
use fixpt_heap::layout::cellular::{CLOSURE_WORD, WORD_CELL0};
use fixpt_heap::{Heap, Value};
use fixpt_scheme::Handle;

/// Every word `word` reaches through its cells and operands.
fn reachable(heap: &Heap, word: Value) -> Vec<Value> {
    let closure = kind("cellular-closure");
    let (mut todo, mut seen, mut out) = (vec![word], std::collections::HashSet::new(), Vec::new());
    while let Some(w) = todo.pop() {
        if !seen.insert(w.raw()) {
            continue;
        }
        out.push(w);
        for v in heap.bloblet_fields_from(w, WORD_CELL0) {
            if heap.is_cellular_word(v) {
                todo.push(v);
            } else if v.is_bloblet() && heap.bloblet_kind(v) == closure {
                todo.push(heap.bloblet_slot(v, CLOSURE_WORD));
            }
        }
    }
    out
}

/// The same instructions from both compilers, for every word of the front
/// end compiled: `limit` words, or all of them.
fn compare(limit: usize) {
    let mut s = common::front_end_session();
    let far = [-5000i64, -6000];
    let (mut wrong, mut compared, mut instructions) = (Vec::new(), 0, 0);
    s.scheme.scope(|sc| {
        // Compiled once for all these tests (`common::bootstrap_compiled`).
        let stage1 = common::bootstrap_compiled(sc, false);
        // Rooted, since running the FX-26 compiler may collect.
        // Walked where nothing can collect: in `make`, which cannot run the
        // engine.
        let mut words = Vec::new();
        sc.make(|m| {
            let w = m.get(stage1);
            words = reachable(m.heap(), w);
            Value::NULL
        });
        let words: Vec<Handle> = words.into_iter().take(limit).map(|w| sc.make(|_| w)).collect();
        let (ft, fe) = (sc.make(|_| Value::fixnum(far[0])), sc.make(|_| Value::fixnum(far[1])));
        for w in words {
            let mut want = (Vec::new(), Vec::new());
            sc.make(|m| {
                let v = m.get(w);
                want = fixpt_native::cellular::assemble_word(m.heap(), v, far).expect("assembles");
                Value::NULL
            });
            let got = sc.scope(|one| {
                let r = one.call_global(&format!("{READER_PREFIX}native-assemble"), &[w, ft, fe]).expect("runs");
                one.view(|v| {
                    let r = v.get(r);
                    let ints = |l: fixpt_scheme::Local| l.list().expect("a list").iter().map(|x| x.fixnum().expect("an int")).collect::<Vec<i64>>();
                    (ints(r.product_field(1).expect("code")), ints(r.product_field(2).expect("starts")))
                })
            });
            compared += 1;
            instructions += want.0.len();
            let want = (want.0.iter().map(|x| *x as i64).collect::<Vec<i64>>(), want.1);
            if got != want {
                let first = got.0.iter().zip(&want.0).position(|(a, b)| a != b);
                wrong.push(format!(
                    "a word of {} instructions (FX-26 {}): first different instruction {first:?}{}",
                    want.0.len(),
                    got.0.len(),
                    first.map(|i| format!(": FX-26 {:#x}, Rust {:#x}", got.0[i], want.0[i])).unwrap_or_default()
                ));
            }
        }
    });
    eprintln!("{compared} words, {instructions} instructions; {} differ", wrong.len());
    assert!(wrong.is_empty(), "{}", wrong.iter().take(10).cloned().collect::<Vec<_>>().join("\n"));
}

#[test]
fn some_words_as_the_rust_compiler_compiles_them() {
    compare(60);
}

#[test]
#[cfg_attr(not(optimized), ignore = "every word of the front end: run with --release")]
fn every_word_of_the_front_end_as_the_rust_compiler_compiles_it() {
    compare(usize::MAX);
}

/// Register code to arm64 by the compiler written in FX-26
/// (`src/native-arm64-regs.fx`) against the Rust one
/// (`fixpt_native::cellular::assemble_register_word`), its oracle: for
/// every register word of the front end compiled with register code, the
/// same instructions and the same resume points, or both refusing it; and
/// the adapters, for every count of arguments. Any machine compiles for
/// arm64.
fn compare_registers(limit: usize) {
    use fixpt_heap::layout::cellular::WORD_TWIN;
    let mut s = common::front_end_session();
    let far = [-5000i64, -6000];
    let slice = fixpt_runtime::sched::slice() as i64;
    let (mut wrong, mut compared, mut refused, mut instructions) = (Vec::new(), 0, 0, 0);
    s.scheme.scope(|sc| {
        // Compiled once for all these tests (`common::bootstrap_compiled`).
        let stage1 = common::bootstrap_compiled(sc, true);
        let mut twins = Vec::new();
        sc.make(|m| {
            let w = m.get(stage1);
            let heap = m.heap();
            twins = reachable(heap, w).into_iter().map(|w| heap.bloblet_slot(w, WORD_TWIN)).filter(|t| heap.is_register_word(*t)).collect();
            Value::NULL
        });
        let twins: Vec<Handle> = twins.into_iter().take(limit).map(|w| sc.make(|_| w)).collect();
        let (ft, fe, sl) = (sc.make(|_| Value::fixnum(far[0])), sc.make(|_| Value::fixnum(far[1])), sc.make(|_| Value::fixnum(slice)));
        let mut progress = common::Progress::new("register words compiled", twins.len());
        for (k, rw) in twins.into_iter().enumerate() {
            progress.at(k);
            let mut want = Err(String::new());
            sc.make(|m| {
                let v = m.get(rw);
                want = fixpt_native::cellular::assemble_register_word(m.heap(), v, far)
                    .map(|(code, resume)| (code.into_iter().map(i64::from).collect::<Vec<i64>>(), resume));
                Value::NULL
            });
            let got = sc.scope(|one| {
                let r = one.call_global(&format!("{READER_PREFIX}native-assemble-arm64-regs"), &[rw, ft, fe, sl]).expect("runs");
                one.view(|v| {
                    let r = v.get(r);
                    let ints = |l: fixpt_scheme::Local| l.list().expect("a list").iter().map(|x| x.fixnum().expect("an int")).collect::<Vec<i64>>();
                    let err = r.product_field(3).and_then(|e| e.string()).unwrap_or_default();
                    if err.is_empty() { Ok((ints(r.product_field(1).expect("code")), ints(r.product_field(2).expect("resume")))) } else { Err(err) }
                })
            });
            compared += 1;
            match (&got, &want) {
                (Ok(g), Ok(w)) if g == w => instructions += w.0.len(),
                (Err(_), Err(_)) => refused += 1,
                (Ok(g), Ok(w)) if g.0 == w.0 => wrong.push("the same instructions, but resume points elsewhere".to_string()),
                (Ok(g), Ok(w)) => {
                    let first = g.0.iter().zip(&w.0).position(|(a, b)| a != b);
                    wrong.push(format!(
                        "a register word of {} instructions (FX-26 {}): first different instruction {first:?}{}",
                        w.0.len(),
                        g.0.len(),
                        first.map(|i| format!(": FX-26 {:#x}, Rust {:#x}", g.0[i], w.0[i])).unwrap_or_default()
                    ));
                }
                (g, w) => wrong.push(format!("FX-26 {:?}, Rust {:?}", g.as_ref().err(), w.as_ref().err())),
            }
        }
        // The adapters.
        for n in 0..=fixpt_heap::layout::regcode::REGS {
            let want: Vec<i64> = fixpt_native::cellular::assemble_adapter(n).into_iter().map(i64::from).collect();
            let got = sc.scope(|one| {
                let a = one.make(|_| Value::fixnum(n as i64));
                let r = one.call_global(&format!("{READER_PREFIX}native-adapter-arm64"), &[a]).expect("runs");
                one.view(|v| v.get(r).list().expect("a list").iter().map(|x| x.fixnum().expect("an int")).collect::<Vec<i64>>())
            });
            if got != want {
                wrong.push(format!("the adapter of {n}: FX-26 {got:x?}, Rust {want:x?}"));
            }
        }
    });
    eprintln!("{compared} register words, {instructions} instructions; {refused} refused by both; {} differ", wrong.len());
    assert!(compared > 0, "no register words");
    assert!(wrong.is_empty(), "{}", wrong.iter().take(10).cloned().collect::<Vec<_>>().join("\n"));
}

#[test]
fn some_register_words_as_the_rust_compiler_compiles_them() {
    compare_registers(60);
}

#[test]
#[cfg_attr(not(optimized), ignore = "every register word of the front end: run with --release")]
fn every_register_word_of_the_front_end_as_the_rust_compiler_compiles_it() {
    compare_registers(usize::MAX);
}
