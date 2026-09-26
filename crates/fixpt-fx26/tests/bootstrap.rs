//! The compiler written in FX-26 compiling the front end written in FX-26,
//! itself included (`PLAN.md` §11, steps 11 and 12).

use fixpt_engine::Backend;
use fixpt_fx26::session::{Fx26Session, load_eager_reader};
use fixpt_read::FileId;

/// The front end, compiled to one threaded word by the compiler written in
/// FX-26 (run lowered to Scheme), with the Rust checker's facts.
#[test]
fn the_compiler_compiles_the_front_end() {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    load_eager_reader(&mut s.scheme).expect("loads");
    s.scheme.engine.set_step_limit(None);
    let text = fixpt_fx26::front_end();
    let t = std::time::Instant::now();
    let r = s.scheme.scope(|sc| {
        let facts = fixpt_fx26::syn::rust_facts(sc, FileId(0), &text).expect("checks");
        fixpt_fx26::syn::compile_to_word(sc, FileId(0), &text, facts).expect("parses").map(|_| ())
    });
    eprintln!("compiled in {:.1} s", t.elapsed().as_secs_f64());
    r.expect("compiles");
}

#[test]
#[ignore = "a probe: the standard names the compiler has no way to run"]
fn probe_uncovered() {
    let compile = fixpt_fx26::COMPILER;
    for (fx, scheme, _) in fixpt_fx26::lower::STANDARD {
        let prim = *scheme == "%fx26-identity" || fixpt_engine::threaded::runtime_primitive(scheme).is_some();
        let special = compile.contains(&format!("\"{fx}\""));
        if !prim && !special {
            eprintln!("{fx} -> {scheme}");
        }
    }
}

#[test]
#[ignore = "a probe: the runtime primitives the compiler names that are not there"]
fn probe_primitives() {
    let compile = fixpt_fx26::COMPILER;
    let mut names: Vec<&str> = Vec::new();
    // `(c-prim c "name" …)` and `(c-prim c name n)` for the names listed
    // with it: every string literal in the compiler that could be one.
    for (i, _) in compile.match_indices('"') {
        let rest = &compile[i + 1..];
        if let Some(end) = rest.find('"') {
            let lit = &rest[..end];
            if !lit.contains(' ') && !lit.is_empty() && !names.contains(&lit) {
                names.push(lit);
            }
        }
    }
    for n in names {
        if fixpt_engine::threaded::runtime_primitive(n).is_none() && fixpt_fx26::lower::STANDARD.iter().any(|(fx, _, _)| *fx == n) {
            eprintln!("standard name without a primitive of its own: {n}");
        }
        if n.starts_with('%') && fixpt_engine::threaded::runtime_primitive(n).is_none() {
            eprintln!("no such primitive: {n}");
        }
    }
}

#[test]
fn the_bootstrap_program_checks() {
    if let Err(e) = fixpt_fx26::session::compile_program_as(&fixpt_fx26::bootstrap_program(), "fx:") {
        let at = e.span.start as usize;
        let text = fixpt_fx26::bootstrap_program();
        let line = text[..at].matches('\n').count() + 1;
        panic!("line {line} of the bootstrap program ({}): {}", &text[at..(at + 60).min(text.len())], e.message);
    }
}

use fixpt_heap::{Heap, Value};
use std::collections::HashMap;

/// Whether words `a` and `b` are the same code: cell for cell, the words
/// they call compared the same way, and each global's cell in one standing
/// for one in the other, consistently. `pairs` is what is assumed so far.
fn same_code(h: &Heap, a: Value, b: Value, pairs: &mut HashMap<u64, u64>, why: &mut String) -> bool {
    if let Some(&x) = pairs.get(&a.raw()) {
        return x == b.raw() || { *why = format!("{} is matched twice", fixpt_runtime::write_value(h, a)); false };
    }
    // Code, and globals' cells, are compared by structure; anything else,
    // a literal, by how it is written.
    let code = |v: Value| {
        v.is_bloblet() && ["threaded-code", "threaded-closure", "bloblet"].iter().any(|k| h.bloblet_kind(v) == fixpt_heap::layout::kind(k))
    };
    let (ka, kb) = (code(a).then(|| h.bloblet_kind(a)), code(b).then(|| h.bloblet_kind(b)));
    if ka.is_none() || kb.is_none() {
        let (wa, wb) = (fixpt_runtime::write_value(h, a), fixpt_runtime::write_value(h, b));
        if wa != wb {
            *why = format!("{wa} and {wb}");
        }
        return wa == wb;
    }
    if ka != kb {
        *why = format!("kinds {ka:?} and {kb:?}");
        return false;
    }
    pairs.insert(a.raw(), b.raw());
    // A global's cell stands for the global; what is in it depends on
    // whether the program has run.
    if ka == Some(fixpt_heap::layout::kind("bloblet")) {
        return true;
    }
    let (na, nb) = (h.bloblet_head(a).fields, h.bloblet_head(b).fields);
    if na != nb {
        *why = format!("{} fields and {}", na, nb);
        return false;
    }
    // Field 1 is the trailer; the rest are values.
    (2..=na).all(|i| same_code(h, h.bloblet_slot(a, i), h.bloblet_slot(b, i), pairs, why))
}

/// The fixpoint: the front end, compiled by the compiler written in FX-26
/// run lowered to Scheme (stage 1), is run on the native machine, and
/// compiles the front end again (stage 2), reading, parsing and checking
/// it itself. The two words must be the same code.
#[test]
#[cfg_attr(debug_assertions, ignore = "10 s in release, 7 minutes in debug: run with --release, or --ignored")]
fn fixpoint() {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    load_eager_reader(&mut s.scheme).expect("loads");
    s.scheme.engine.set_step_limit(None);
    s.scheme.runtime_unrooted().run_word = Some(fixpt_native::threaded::run_word);
    let text = fixpt_fx26::bootstrap_program();
    let standard: String = fixpt_fx26::standard::ENTRIES.iter().map(|(n, t)| format!("({n} {t})\n")).collect();
    let t = std::time::Instant::now();
    let lap = |what: &str| eprintln!("{what}: {:.1} s", t.elapsed().as_secs_f64());
    s.scheme.scope(|sc| {
        let facts = fixpt_fx26::syn::rust_facts(sc, FileId(0), &text).expect("checks");
        let stage1 = fixpt_fx26::syn::compile_to_word(sc, FileId(0), &text, facts).expect("parses").expect("compiles");
        lap("stage 1 compiled, by the compiler run lowered");
        let none = sc.make(|_| Value::NULL);
        let pieces = sc.call_global("%run-word", &[stage1, none]).expect("the front end runs");
        let driver = sc.make(|m| { let p = m.get(pieces); m.heap().bloblet_slot(p, 2) });
        lap("the compiled front end ran, giving the driver");
        let (std, prog) = (sc.make(|m| m.heap().make_string(&standard)), sc.make(|m| m.heap().make_string(&text)));
        let args = sc.call_global("list", &[std, prog]).expect("a list");
        let result = sc.call_global("%run-word", &[driver, args]).expect("the driver runs");
        lap("stage 2 compiled, by the compiler compiled");
        let (tag, stage2) = sc.view(|v| {
            let r = v.get(result);
            let tag = r.field(2).and_then(|t| t.symbol_name()).unwrap_or_default();
            let why = r.field(3).and_then(|p| p.field(2)).and_then(|x| x.string()).unwrap_or_default();
            (tag, why)
        });
        assert_eq!(tag, "b-word", "stage 2 failed: {stage2:?}");
        // Compared where nothing can collect: in `make`, which cannot run
        // the engine.
        let (mut same, mut why) = (false, String::new());
        sc.make(|m| {
            let a = m.get(stage1);
            let r = m.get(result);
            let h = m.heap();
            let b = h.bloblet_slot(h.bloblet_slot(r, 3), 2);
            same = same_code(h, a, b, &mut HashMap::new(), &mut why);
            Value::NULL
        });
        assert!(same, "stage 1 and stage 2 differ: {why}");
        lap("stage 1 and stage 2 are the same code");
    });
}

/// The compiled driver on one program (`PROBE_FILE`, else `table.fx`), timed,
/// with the native machine's call-outs (`FIXPT_CALLOUTS=1`).
#[test]
#[ignore = "a probe: FIXPT_CALLOUTS=1 cargo test -p fixpt-fx26 --test bootstrap probe_stage2 -- --ignored --nocapture"]
fn probe_stage2() {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    load_eager_reader(&mut s.scheme).expect("loads");
    s.scheme.engine.set_step_limit(None);
    s.scheme.runtime_unrooted().run_word = Some(fixpt_native::threaded::run_word);
    let text = fixpt_fx26::bootstrap_program();
    let target = match std::env::var("PROBE_FILE") {
        Ok(p) if p == "front-end" => text.clone(),
        Ok(p) => std::fs::read_to_string(p).unwrap(),
        Err(_) => fixpt_fx26::TABLE.to_string(),
    };
    let standard: String = fixpt_fx26::standard::ENTRIES.iter().map(|(n, t)| format!("({n} {t})\n")).collect();
    s.scheme.scope(|sc| {
        let facts = fixpt_fx26::syn::rust_facts(sc, FileId(0), &text).expect("checks");
        let stage1 = fixpt_fx26::syn::compile_to_word(sc, FileId(0), &text, facts).expect("parses").expect("compiles");
        let none = sc.make(|_| Value::NULL);
        let pieces = sc.call_global("%run-word", &[stage1, none]).expect("runs");
        let driver = sc.make(|m| { let p = m.get(pieces); m.heap().bloblet_slot(p, 2) });
        let _ = fixpt_native::threaded::take_callout_counts();
        let _ = fixpt_native::threaded::take_callout_nanos();
        let (std, prog) = (sc.make(|m| m.heap().make_string(&standard)), sc.make(|m| m.heap().make_string(&target)));
        let args = sc.call_global("list", &[std, prog]).expect("a list");
        let gc = |sc: &mut fixpt_scheme::Session| {
            let (n, w) = (sc.call_global("%gc-count", &[]).unwrap(), sc.call_global("%gc-words-copied", &[]).unwrap());
            sc.view(|v| (v.get(n).fixnum().unwrap_or(0), v.get(w).fixnum().unwrap_or(0)))
        };
        let before = gc(sc);
        let t = std::time::Instant::now();
        let result = sc.call_global("%run-word", &[driver, args]).expect("the driver runs");
        eprintln!("the compiled driver: {:.2} s", t.elapsed().as_secs_f64());
        let after = gc(sc);
        eprintln!("collections: {}, words copied: {}, heap in use: {} words", after.0 - before.0, after.1 - before.1, sc.heap_used());
        let tag = sc.view(|v| v.get(result).field(2).and_then(|t| t.symbol_name()).unwrap_or_default());
        assert_eq!(tag, "b-word");
    });
}

/// The pieces, each alone, on the same input (the bootstrap program): the
/// Rust ones, the FX-26 ones lowered to Scheme, and the FX-26 ones compiled
/// and run on each threaded machine. A table, for `docs/performance.md`.
#[test]
#[ignore = "a report: cargo test --release -p fixpt-fx26 --test bootstrap comparison -- --ignored --nocapture"]
fn comparison() {
    use fixpt_fx26::session::{BOOTSTRAP_PREFIX, load_bootstrap_program};
    use fixpt_scheme::{Handle, Session};
    let text = fixpt_fx26::bootstrap_program();
    let standard: String = fixpt_fx26::standard::ENTRIES.iter().map(|(n, t)| format!("({n} {t})\n")).collect();
    let mut rows: Vec<(String, [f64; 4])> = Vec::new();

    // Rust: reading, then checking, which parses as it goes.
    let t = std::time::Instant::now();
    let mut c = fixpt_fx26::Checker::new();
    let forms = c.read_in(FileId(0), &text).expect("reads");
    let read = t.elapsed().as_secs_f64();
    let t = std::time::Instant::now();
    let done = c.declare_ahead(&forms).expect("declares");
    for (f, done) in forms.iter().zip(done) {
        if !done {
            c.top(f).expect("checks");
        }
    }
    let check = t.elapsed().as_secs_f64();
    rows.push(("Rust".into(), [read, f64::NAN, check, f64::NAN]));

    // The four phases, through `run`: how one piece is called.
    fn phases(sc: &mut Session, text: &str, standard: &str, run: &dyn Fn(&mut Session, usize, &[Handle]) -> Handle) -> [f64; 4] {
        let (tx, st) = (sc.make(|m| m.heap().make_string(text)), sc.make(|m| m.heap().make_string(standard)));
        let payload = |sc: &mut Session, h: Handle| sc.make(|m| { let r = m.get(h); let p = m.heap().bloblet_slot(r, 3); m.heap().bloblet_slot(p, 2) });
        let first = |sc: &mut Session, h: Handle| sc.make(|m| { let l = m.get(h); m.heap().car(l) });
        let copied = |sc: &mut Session| {
            let w = sc.call_global("%gc-words-copied", &[]).unwrap();
            sc.view(|v| v.get(w).fixnum().unwrap_or(0))
        };
        let c0 = copied(sc);
        let t = std::time::Instant::now();
        let syns = run(sc, 1, &[tx]);
        let read = t.elapsed().as_secs_f64();
        eprintln!("  reading: {:.0} M words copied by the collector, {} M words in use", (copied(sc) - c0) as f64 / 1e6, sc.heap_used() / 1_000_000);
        let syns = first(sc, syns);
        let std = run(sc, 1, &[st]);
        let std = first(sc, std);
        let t = std::time::Instant::now();
        let parsed = run(sc, 2, &[syns]);
        let parse = t.elapsed().as_secs_f64();
        let tops = payload(sc, parsed);
        let t = std::time::Instant::now();
        run(sc, 3, &[std, tops]);
        let check = t.elapsed().as_secs_f64();
        let facts = run(sc, 5, &[]);
        let t = std::time::Instant::now();
        run(sc, 4, &[tops, facts]);
        let compile = t.elapsed().as_secs_f64();
        [read, parse, check, compile]
    }
    const NAMES: [&str; 6] = ["bootstrap", "b-read", "parse-program", "check-program", "compile-program", "checked-extracts"];

    // Lowered to Scheme, on the bytecode VM.
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    s.scheme.engine.set_step_limit(None);
    load_bootstrap_program(&mut s.scheme).expect("loads");
    s.scheme.collect();
    let lowered = s.scheme.scope(|sc| {
        phases(sc, &text, &standard, &|sc, i, args| {
            sc.call_global(&format!("{BOOTSTRAP_PREFIX}{}", NAMES[i]), args).expect("runs")
        })
    });
    rows.push(("FX-26, lowered to Scheme".into(), lowered));

    // Compiled, on each machine.
    type Run = fn(&mut fixpt_runtime::Runtime, Value, &[Value]) -> Result<Value, String>;
    let machines: [(&str, Run); 3] = [
        ("Rust machine", fixpt_engine::threaded::run_word),
        ("hand-encoded machine", fixpt_native::threaded::run_word),
        ("stencils, -O2", fixpt_native::stencil::run_word),
    ];
    for (name, machine) in machines {
        let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
        load_eager_reader(&mut s.scheme).expect("loads");
        s.scheme.engine.set_step_limit(None);
        s.scheme.runtime_unrooted().run_word = Some(machine);
        let times = s.scheme.scope(|sc| {
            // Stage 1 in a scope of its own, so that what it leaves (the Rust
            // driver's reader states, above all) is garbage before timing.
            let pieces = sc.make(|_| Value::NULL);
            sc.scope(|inner| {
                let facts = fixpt_fx26::syn::rust_facts(inner, FileId(0), &text).expect("checks");
                let stage1 = fixpt_fx26::syn::compile_to_word(inner, FileId(0), &text, facts).expect("parses").expect("compiles");
                let none = inner.make(|_| Value::NULL);
                let made = inner.call_global("%run-word", &[stage1, none]).expect("runs");
                inner.replace(pieces, |m| m.get(made));
            });
            sc.collect();
            phases(sc, &text, &standard, &|sc, i, args| {
                let f = sc.make(|m| { let p = m.get(pieces); m.heap().bloblet_slot(p, 2 + i) });
                let list = sc.call_global("list", args).expect("a list");
                sc.call_global("%run-word", &[f, list]).expect("runs")
            })
        });
        rows.push((format!("FX-26, compiled, {name}"), times));
    }

    eprintln!("| pieces | read | parse | check | compile |");
    for (name, t) in rows {
        let cell = |x: f64| if x.is_nan() { "—".to_string() } else { format!("{x:.2} s") };
        eprintln!("| {name} | {} | {} | {} | {} |", cell(t[0]), cell(t[1]), cell(t[2]), cell(t[3]));
    }
}

/// The compiled reader alone, on the hand-encoded machine, ten times over
/// the bootstrap program: something to sample.
#[test]
#[ignore = "a probe: cargo test --release -p fixpt-fx26 --test bootstrap probe_read -- --ignored --nocapture"]
fn probe_read() {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    load_eager_reader(&mut s.scheme).expect("loads");
    s.scheme.engine.set_step_limit(None);
    s.scheme.runtime_unrooted().run_word = Some(fixpt_native::threaded::run_word);
    let text = fixpt_fx26::bootstrap_program();
    s.scheme.scope(|sc| {
        let pieces = sc.make(|_| Value::NULL);
        sc.scope(|inner| {
            let facts = fixpt_fx26::syn::rust_facts(inner, FileId(0), &text).expect("checks");
            let stage1 = fixpt_fx26::syn::compile_to_word(inner, FileId(0), &text, facts).expect("parses").expect("compiles");
            let none = inner.make(|_| Value::NULL);
            let made = inner.call_global("%run-word", &[stage1, none]).expect("runs");
            inner.replace(pieces, |m| m.get(made));
        });
        sc.collect();
        let read = sc.make(|m| { let p = m.get(pieces); m.heap().bloblet_slot(p, 3) });
        let tx = sc.make(|m| m.heap().make_string(&text));
        let args = sc.call_global("list", &[tx]).expect("a list");
        eprintln!("reading");
        for _ in 0..10 {
            let t = std::time::Instant::now();
            sc.scope(|one| {
                one.call_global("%run-word", &[read, args]).expect("reads");
            });
            eprintln!("read: {:.2} s", t.elapsed().as_secs_f64());
        }
    });
}
