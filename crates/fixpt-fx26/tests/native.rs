//! Words compiled to machine code by the compiler written in FX-26
//! (`src/native.fx`) against the Rust one (`fixpt_native::cellular::
//! assemble_word`), its oracle: for every word of the bootstrap program,
//! compiled, the same instructions and the same places where each cell's
//! code starts (`PLAN.md` §11, 11c).

use fixpt_engine::Backend;
use fixpt_fx26::session::{Fx26Session, READER_PREFIX, load_eager_reader};
use fixpt_heap::layout::kind;
use fixpt_heap::layout::cellular::{CLOSURE_WORD, WORD_CELL0};
use fixpt_heap::{Heap, Value};
use fixpt_read::FileId;
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

/// The same instructions from both compilers, for every word of the front
/// end compiled: `limit` words, or all of them.
fn compare(limit: usize) {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    load_eager_reader(&mut s.scheme).expect("loads");
    s.scheme.engine.set_step_limit(None);
    let text = fixpt_fx26::bootstrap_program();
    let far = [-5000i64, -6000];
    let (mut wrong, mut compared, mut instructions) = (Vec::new(), 0, 0);
    s.scheme.scope(|sc| {
        let facts = fixpt_fx26::syn::rust_facts(sc, FileId(0), &text).expect("checks");
        let stage1 = fixpt_fx26::syn::compile_to_word(sc, FileId(0), &text, facts).expect("parses").expect("compiles");
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
                    (ints(r.field(2).expect("code")), ints(r.field(3).expect("starts")))
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
#[cfg_attr(debug_assertions, ignore = "every word of the front end: run with --release")]
fn every_word_of_the_front_end_as_the_rust_compiler_compiles_it() {
    compare(usize::MAX);
}
