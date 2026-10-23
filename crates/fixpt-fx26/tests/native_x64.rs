//! Words compiled to x86_64 machine code by the compiler written in FX-26
//! (`src/native-x64.fx`) against the Rust one (`fixpt_native::cellular::
//! x64::assemble_word`), its oracle: for every word of the bootstrap
//! program, compiled, the same bytes and the same places where each cell's
//! code starts, as `tests/native.rs` checks `native.fx` for arm64. Any
//! machine compiles for x86_64; none runs the code here.

mod common;

use fixpt_fx26::session::READER_PREFIX;
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
    let mut s = common::front_end_session();
    let text = fixpt_fx26::bootstrap_program();
    let (mut wrong, mut compared, mut bytes) = (Vec::new(), 0, 0);
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
        let mut progress = common::Progress::new("words compiled", words.len());
        for (k, w) in words.into_iter().enumerate() {
            progress.at(k);
            let mut want = (Vec::new(), Vec::new());
            sc.make(|m| {
                let v = m.get(w);
                let (code, starts) = fixpt_native::cellular::x64::assemble_word(m.heap(), v).expect("assembles");
                want = (code.into_iter().map(i64::from).collect::<Vec<i64>>(), starts);
                Value::NULL
            });
            let got = sc.scope(|one| {
                let r = one.call_global(&format!("{READER_PREFIX}native-assemble-x64"), &[w]).expect("runs");
                one.view(|v| {
                    let r = v.get(r);
                    let ints = |l: fixpt_scheme::Local| l.list().expect("a list").iter().map(|x| x.fixnum().expect("an int")).collect::<Vec<i64>>();
                    (ints(r.field(2).expect("code")), ints(r.field(3).expect("starts")))
                })
            });
            compared += 1;
            bytes += want.0.len();
            if got.1 != want.1 && got.0 == want.0 {
                wrong.push("the same bytes, but cells starting elsewhere".into());
            } else if got != want {
                let first = got.0.iter().zip(&want.0).position(|(a, b)| a != b);
                wrong.push(format!(
                    "a word of {} bytes (FX-26 {}): first different byte {first:?}{}",
                    want.0.len(),
                    got.0.len(),
                    first.map(|i| format!(": FX-26 {:#04x}, Rust {:#04x}", got.0[i], want.0[i])).unwrap_or_default()
                ));
            }
        }
    });
    eprintln!("{compared} words, {bytes} bytes; {} differ", wrong.len());
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

/// Register code to x86_64 by the compiler written in FX-26
/// (`src/native-x64-regs.fx`) against the Rust one
/// (`fixpt_native::cellular::x64::assemble_register_word`), its oracle: for
/// every register word of the front end compiled with register code, the
/// same bytes and the same resume points, or both refusing it; and the
/// adapters, for every count of arguments.
fn compare_registers(limit: usize) {
    use fixpt_heap::layout::cellular::WORD_TWIN;
    let mut s = common::front_end_session();
    let text = fixpt_fx26::bootstrap_program();
    let (mut wrong, mut compared, mut refused, mut bytes) = (Vec::new(), 0, 0, 0);
    s.scheme.scope(|sc| {
        let facts = fixpt_fx26::syn::rust_facts(sc, FileId(0), &text).expect("checks");
        let stage1 = fixpt_fx26::syn::compile_to_word_with_registers(sc, FileId(0), &text, facts).expect("parses").expect("compiles");
        let mut twins = Vec::new();
        sc.make(|m| {
            let w = m.get(stage1);
            let heap = m.heap();
            twins = reachable(heap, w).into_iter().map(|w| heap.bloblet_slot(w, WORD_TWIN)).filter(|t| heap.is_register_word(*t)).collect();
            Value::NULL
        });
        let twins: Vec<Handle> = twins.into_iter().take(limit).map(|w| sc.make(|_| w)).collect();
        let mut progress = common::Progress::new("register words compiled", twins.len());
        for (k, rw) in twins.into_iter().enumerate() {
            progress.at(k);
            let mut want = Err(String::new());
            sc.make(|m| {
                let v = m.get(rw);
                want = fixpt_native::cellular::x64::assemble_register_word(m.heap(), v)
                    .map(|(code, resume)| (code.into_iter().map(i64::from).collect::<Vec<i64>>(), resume));
                Value::NULL
            });
            let got = sc.scope(|one| {
                let r = one.call_global(&format!("{READER_PREFIX}native-assemble-x64-regs"), &[rw]).expect("runs");
                one.view(|v| {
                    let r = v.get(r);
                    let ints = |l: fixpt_scheme::Local| l.list().expect("a list").iter().map(|x| x.fixnum().expect("an int")).collect::<Vec<i64>>();
                    let err = r.field(4).and_then(|e| e.string()).unwrap_or_default();
                    if err.is_empty() { Ok((ints(r.field(2).expect("code")), ints(r.field(3).expect("resume")))) } else { Err(err) }
                })
            });
            compared += 1;
            match (&got, &want) {
                (Ok(g), Ok(w)) if g == w => bytes += w.0.len(),
                (Err(_), Err(_)) => refused += 1,
                (Ok(g), Ok(w)) if g.0 == w.0 => wrong.push("the same bytes, but resume points elsewhere".to_string()),
                (Ok(g), Ok(w)) => {
                    let first = g.0.iter().zip(&w.0).position(|(a, b)| a != b);
                    wrong.push(format!(
                        "a register word of {} bytes (FX-26 {}): first different byte {first:?}{}",
                        w.0.len(),
                        g.0.len(),
                        first.map(|i| format!(": FX-26 {:#04x}, Rust {:#04x}", g.0[i], w.0[i])).unwrap_or_default()
                    ));
                }
                (g, w) => wrong.push(format!("FX-26 {:?}, Rust {:?}", g.as_ref().err(), w.as_ref().err())),
            }
        }
        // The adapters.
        for n in 0..=fixpt_heap::layout::regcode::REGS {
            for slot in [0usize, 1, 37, 300] {
                let want: Vec<i64> = fixpt_native::cellular::x64::assemble_adapter(n, slot).into_iter().map(i64::from).collect();
                let got = sc.scope(|one| {
                    let (a, b) = (one.make(|_| Value::fixnum(n as i64)), one.make(|_| Value::fixnum(slot as i64)));
                    let r = one.call_global(&format!("{READER_PREFIX}native-adapter-x64"), &[a, b]).expect("runs");
                    one.view(|v| v.get(r).list().expect("a list").iter().map(|x| x.fixnum().expect("an int")).collect::<Vec<i64>>())
                });
                if got != want {
                    wrong.push(format!("the adapter of {n} for slot {slot}: FX-26 {got:02x?}, Rust {want:02x?}"));
                }
            }
        }
    });
    eprintln!("{compared} register words, {bytes} bytes; {refused} refused by both; {} differ", wrong.len());
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

/// The native convention's procedures compiled to x86_64 by the compiler
/// written in FX-26 (`src/native-direct-x64.fx`) against the Rust one
/// (`fixpt_native::direct`'s `procedure_x64`), its oracle: every register
/// word of the front end compiled with register code, each as a closure
/// of its own, its procedure the same bytes, the same fields and the same
/// call-outs as Rust makes it, or both refusing it (`compile_each`,
/// `fx_begin_each`, its own procedure only). `limit` words, or all of
/// them. Each machine compiles only these, in order, so their call-outs
/// are numbered alike.
fn compare_direct(limit: usize) {
    use fixpt_heap::layout::cellular::{CLOSURE_WORD, WORD_TWIN};
    use fixpt_native::direct::DirectMachine;
    let mut s = common::front_end_session();
    let text = fixpt_fx26::bootstrap_program();
    let (mut wrong, mut compared, mut refused, mut bytes) = (Vec::new(), 0, 0, 0);
    s.scheme.scope(|sc| {
        let facts = fixpt_fx26::syn::rust_facts(sc, FileId(0), &text).expect("checks");
        let stage1 = fixpt_fx26::syn::compile_to_word_with_registers(sc, FileId(0), &text, facts).expect("parses").expect("compiles");
        let mut words = Vec::new();
        sc.make(|m| {
            let w = m.get(stage1);
            let heap = m.heap();
            words = reachable(heap, w).into_iter().filter(|w| heap.is_register_word(heap.bloblet_slot(*w, WORD_TWIN))).collect();
            Value::NULL
        });
        let words: Vec<Handle> = words.into_iter().take(limit).map(|w| sc.make(|_| w)).collect();
        let (mut rust, mut fx) = (DirectMachine::new().expect("a machine"), DirectMachine::new().expect("a machine"));
        let mut progress = common::Progress::new("procedures compiled", words.len());
        for (k, w) in words.into_iter().enumerate() {
            progress.at(k);
            let clo = sc.make(|m| {
                let w = m.get(w);
                let h = m.heap();
                let c = h.make_bloblet(kind("cellular-closure"), 1, 0, true);
                h.set_bloblet_slot(c, CLOSURE_WORD, w);
                c
            });
            match compare_one(sc, clo, &mut rust, &mut fx) {
                Ok(None) => refused += 1,
                Ok(Some(n)) => bytes += n,
                Err(e) => wrong.push(e),
            }
            compared += 1;
        }
        if rust.callout_codes() != fx.callout_codes() && wrong.is_empty() {
            wrong.push("the call-outs differ".into());
        }
    });
    eprintln!("{compared} procedures, {bytes} bytes; {refused} refused by both; {} differ", wrong.len());
    assert!(compared > 0, "no procedures");
    assert!(wrong.is_empty(), "{}", wrong.iter().take(10).cloned().collect::<Vec<_>>().join("\n"));
}

/// Closure `clo`'s own procedure, compiled by both: its bytes' count if
/// they agree, none if both refuse it, or what differs.
fn compare_one(sc: &mut fixpt_scheme::Session, clo: Handle, rust: &mut fixpt_native::direct::DirectMachine, fx: &mut fixpt_native::direct::DirectMachine) -> Result<Option<usize>, String> {
    use fixpt_native::direct::{Each, FxEmitted};
    let mut want: Vec<Each> = Vec::new();
    sc.make(|m| {
        let v = m.get(clo);
        want = rust.compile_each(m.heap(), v, true).expect("compiles");
        Value::NULL
    });
    // The values Rust's fields hold, held while FX-26 runs.
    let held: Vec<Vec<Handle>> = match &want[0].1 {
        Ok((_, _, fs)) => fs.iter().map(|(_, vs)| vs.iter().map(|&v| sc.make(|_| v)).collect()).collect(),
        Err(_) => Vec::new(),
    };
    let mut begun = None;
    sc.make(|m| {
        let v = m.get(clo);
        begun = Some(fx.fx_begin_each(m.heap(), v, true).expect("begins"));
        Value::NULL
    });
    let mut c = begun.expect("begun");
    loop {
        let mut next = Ok(None);
        sc.make(|m| {
            next = fx.fx_next(m.heap(), &mut c);
            Value::NULL
        });
        let Some(req) = next.expect("asks") else { break };
        let name = sc.make(|m| m.heap().make_string(&req.name));
        let lists = sc.make(|m| {
            let heap = m.heap();
            let lists: Vec<Value> = [&req.head, &req.hi, &req.lo, &req.ids, &req.kind, &req.a, &req.b, &req.c_hi, &req.c_lo]
                .iter()
                .map(|l| {
                    let items: Vec<Value> = l.iter().map(|&x| Value::fixnum(x)).collect();
                    heap.list_from(&items)
                })
                .collect();
            heap.list_from(&lists)
        });
        let errors = sc.make(|m| {
            let heap = m.heap();
            let items: Vec<Value> = req.errors.iter().map(|e| heap.make_string(e)).collect();
            heap.list_from(&items)
        });
        sc.make(|m| {
            fx.fx_park(m.heap(), &mut c);
            Value::NULL
        });
        let made = sc.call_global(&format!("{READER_PREFIX}native-compile-x64-proc"), &[name, lists, errors]).expect("runs");
        sc.make(|m| {
            fx.fx_unpark(m.heap(), &mut c);
            Value::NULL
        });
        let out = sc.view(|v| {
            let r = v.get(made);
            let ints = |k: usize| r.field(k).and_then(|l| l.list()).unwrap_or_default().iter().filter_map(|x| x.fixnum()).collect::<Vec<i64>>();
            FxEmitted {
                code: ints(2).into_iter().map(|b| b as u8).collect(),
                len: r.field(3).and_then(|l| l.fixnum()).unwrap_or(0) as usize,
                fields: ints(4),
                callouts: ints(5),
                err: r.field(6).and_then(|e| e.string()).unwrap_or_default(),
            }
        });
        sc.make(|m| {
            fx.fx_emitted(m.heap(), &mut c, out).expect("takes it");
            Value::NULL
        });
    }
    let shown = |vs: &[Value]| vs.iter().map(|v| format!("{:#x}", v.raw())).collect::<Vec<_>>().join(" ");
    let mut got: Vec<Each> = Vec::new();
    let mut want_fields = Vec::new();
    sc.make(|m| {
        got = fx.fx_each(m.heap(), c);
        if let Ok((_, _, fs)) = &want[0].1 {
            want_fields = fs.iter().zip(&held).map(|((what, _), hs)| format!("{what} {}", shown(&hs.iter().map(|h| m.get(*h)).collect::<Vec<_>>()))).collect::<Vec<String>>();
        }
        Value::NULL
    });
    let name = &want[0].0;
    match (&want[0].1, &got[0].1) {
        (Err(a), Err(b)) if a == b => Ok(None),
        (Ok((wc, wl, _)), Ok((gc, gl, gf))) => {
            let gs: Vec<String> = gf.iter().map(|(what, vs)| format!("{what} {}", shown(vs))).collect();
            if (wc, wl) != (gc, gl) {
                let first = wc.iter().zip(gc).position(|(a, b)| a != b);
                Err(format!("`{name}` ({} bytes, FX-26 {}): first different byte {first:?}", wc.len(), gc.len()))
            } else if want_fields != gs {
                Err(format!("`{name}`: fields Rust {want_fields:?}, FX-26 {gs:?}"))
            } else {
                Ok(Some(wc.len()))
            }
        }
        (w, g) => Err(format!("`{name}`: Rust {:?}, FX-26 {:?}", w.as_ref().err(), g.as_ref().err())),
    }
}

#[test]
fn some_procedures_as_the_rust_compiler_compiles_them() {
    compare_direct(60);
}

#[test]
#[cfg_attr(not(optimized), ignore = "every procedure of the front end: run with --release")]
fn every_procedure_of_the_front_end_as_the_rust_compiler_compiles_it() {
    compare_direct(usize::MAX);
}
