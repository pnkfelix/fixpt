//! The compiler written in FX-26 compiling the front end written in FX-26,
//! itself included (`PLAN.md` §11, steps 11 and 12).

use fixpt_engine::Backend;
use fixpt_fx26::session::{Fx26Session, load_eager_reader};
use fixpt_read::FileId;

/// The front end, compiled to one cellular word by the compiler written in
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
        let prim = *scheme == "%fx26-identity" || fixpt_engine::cellular::runtime_primitive(scheme).is_some();
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
        if fixpt_engine::cellular::runtime_primitive(n).is_none() && fixpt_fx26::lower::STANDARD.iter().any(|(fx, _, _)| *fx == n) {
            eprintln!("standard name without a primitive of its own: {n}");
        }
        if n.starts_with('%') && fixpt_engine::cellular::runtime_primitive(n).is_none() {
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

mod common;
use common::same_code;

/// The fixpoint: the front end, compiled by the compiler written in FX-26
/// run lowered to Scheme (stage 1), is run on the native machine, and
/// compiles the front end again (stage 2), reading, parsing and checking
/// it itself. The two words must be the same code.
#[test]
#[cfg_attr(debug_assertions, ignore = "4 s in release, 7 minutes in debug: run with --release, or --ignored")]
fn fixpoint() {
    fixpoint_on(fixpt_native::cellular::run_word);
}

/// The same, with stage 2's words compiled to machine code (step 11a) as
/// they run: it must make the same code.
#[test]
#[cfg_attr(debug_assertions, ignore = "4 s in release, 7 minutes in debug: run with --release, or --ignored")]
fn fixpoint_with_words_compiled() {
    fixpoint_on(fixpt_native::cellular::run_word_compiled);
}

/// The same, with stage 1 made by the compiler written in Rust, register
/// code and all (PLAN.md 13h′), and run as register code: the front end,
/// run so, must compile itself to the same code.
#[test]
#[cfg_attr(debug_assertions, ignore = "seconds in release: run with --release, or --ignored")]
fn fixpoint_as_register_code() {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    load_eager_reader(&mut s.scheme).expect("loads");
    s.scheme.engine.set_step_limit(None);
    s.scheme.runtime_unrooted().run_word = Some(fixpt_native::cellular::run_word_registers);
    if let Some(n) = std::env::var("FIXPT_GC_EVERY").ok().and_then(|n| n.parse().ok()) {
        s.scheme.set_gc_every(n);
    }
    let text = fixpt_fx26::bootstrap_program();
    let standard: String = fixpt_fx26::standard::ENTRIES.iter().map(|(n, t)| format!("({n} {t})\n")).collect();
    let mut c = fixpt_fx26::Checker::new();
    let forms = c.read_in(FileId(0), &text).expect("reads");
    let done = c.declare_ahead(&forms).expect("declares");
    let tops: Vec<_> = forms.iter().zip(done).filter(|(_, d)| !d).flat_map(|(f, _)| c.top_all(f).expect("checks")).collect();
    let t = std::time::Instant::now();
    let lap = |what: &str| eprintln!("{what}: {:.2} s", t.elapsed().as_secs_f64());
    s.scheme.scope(|sc| {
        let stage1 = sc.make(|m| {
            let mut comp = fixpt_fx26::cellular::Compiler::new(m.heap(), &c, &text);
            comp.registers = true;
            comp.program(&tops).expect("compiles")
        });
        lap("stage 1 compiled by the Rust compiler, with register code");
        let none = sc.make(|_| Value::NULL);
        let pieces = sc.call_global("%run-word", &[stage1, none]).expect("the front end runs");
        let driver = sc.make(|m| { let p = m.get(pieces); m.heap().bloblet_slot(p, 2) });
        // Stage 2 with register code too, by the register compiler written
        // in FX-26 (`regcode.fx`): its twins the same as the Rust one's.
        let registers = sc.make(|m| { let p = m.get(pieces); m.heap().bloblet_slot(p, 9) });
        let on = sc.make(|_| Value::TRUE);
        let on = sc.call_global("list", &[on]).expect("a list");
        sc.call_global("%run-word", &[registers, on]).expect("register code on");
        let (std, prog) = (sc.make(|m| m.heap().make_string(&standard)), sc.make(|m| m.heap().make_string(&text)));
        let args = sc.call_global("list", &[std, prog]).expect("a list");
        let result = sc.call_global("%run-word", &[driver, args]).expect("the driver runs");
        lap("stage 2 compiled, with register code, by the compiler run as register code");
        if std::env::var_os("FIXPT_GC_REPORT").is_some() {
            let h = &sc.runtime_unrooted().heap;
            eprintln!(
                "collections {}, {:.1} ms; words allocated {}, copied {}; semispace now {} words",
                h.gc_count, h.gc_nanos as f64 / 1e6, h.allocated(), h.words_copied, h.semispace_words()
            );
        }
        let (tag, stage2) = sc.view(|v| {
            let r = v.get(result);
            let tag = r.field(2).and_then(|t| t.symbol_name()).unwrap_or_default();
            let why = r.field(3).and_then(|p| p.field(2)).and_then(|x| x.string()).unwrap_or_default();
            (tag, why)
        });
        assert_eq!(tag, "b-word", "stage 2 failed: {stage2:?}");
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
    });
}

fn fixpoint_on(machine: fixpt_runtime::RunWord) {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    load_eager_reader(&mut s.scheme).expect("loads");
    s.scheme.engine.set_step_limit(None);
    s.scheme.runtime_unrooted().run_word = Some(machine);
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
    s.scheme.runtime_unrooted().run_word = Some(fixpt_native::cellular::run_word);
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
        let _ = fixpt_native::cellular::take_callout_counts();
        let _ = fixpt_native::cellular::take_callout_nanos();
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
/// and run on each cellular machine. A table, for `docs/performance.md`.
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
            c.top_defining(f).expect("checks");
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
        ("Rust machine", fixpt_engine::cellular::run_word),
        ("hand-encoded machine", fixpt_native::cellular::run_word),
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

    // Compiled to machine code as they run: stack code (C11a), and register
    // code (PLAN.md 13h′), whose stage 1 the Rust compiler makes, since only
    // it makes register code yet. Each is run once first, to compile what
    // it runs; the second run is timed.
    for (name, registers) in [("words compiled", false), ("register code", true)] {
        let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
        load_eager_reader(&mut s.scheme).expect("loads");
        s.scheme.engine.set_step_limit(None);
        s.scheme.runtime_unrooted().run_word =
            Some(if registers { fixpt_native::cellular::run_word_registers } else { fixpt_native::cellular::run_word_compiled });
        let times = s.scheme.scope(|sc| {
            let pieces = sc.make(|_| Value::NULL);
            sc.scope(|inner| {
                let stage1 = if registers {
                    let mut c = fixpt_fx26::Checker::new();
                    let forms = c.read_in(FileId(0), &text).expect("reads");
                    let done = c.declare_ahead(&forms).expect("declares");
                    let tops: Vec<_> = forms.iter().zip(done).filter(|(_, d)| !d).flat_map(|(f, _)| c.top_all(f).expect("checks")).collect();
                    inner.make(|m| {
                        let mut comp = fixpt_fx26::cellular::Compiler::new(m.heap(), &c, &text);
                        comp.registers = true;
                        comp.program(&tops).expect("compiles")
                    })
                } else {
                    let facts = fixpt_fx26::syn::rust_facts(inner, FileId(0), &text).expect("checks");
                    fixpt_fx26::syn::compile_to_word(inner, FileId(0), &text, facts).expect("parses").expect("compiles")
                };
                let none = inner.make(|_| Value::NULL);
                let made = inner.call_global("%run-word", &[stage1, none]).expect("runs");
                inner.replace(pieces, |m| m.get(made));
            });
            sc.collect();
            let run = |sc: &mut Session, i: usize, args: &[Handle]| {
                let f = sc.make(|m| { let p = m.get(pieces); m.heap().bloblet_slot(p, 2 + i) });
                let list = sc.call_global("list", args).expect("a list");
                sc.call_global("%run-word", &[f, list]).expect("runs")
            };
            phases(sc, &text, &standard, &run);
            phases(sc, &text, &standard, &run)
        });
        rows.push((format!("FX-26, {name}"), times));
    }

    eprintln!("| pieces | read | parse | check | compile |");
    for (name, t) in rows {
        let cell = |x: f64| if x.is_nan() { "—".to_string() } else { format!("{x:.2} s") };
        eprintln!("| {name} | {} | {} | {} | {} |", cell(t[0]), cell(t[1]), cell(t[2]), cell(t[3]));
    }
}

/// The compiled reader alone, as register code, ten times over the
/// bootstrap program: something to sample, or to count the call-outs of
/// (`FIXPT_CALLOUTS=1`).
#[test]
#[ignore = "a probe: cargo test --release -p fixpt-fx26 --test bootstrap probe_read -- --ignored --nocapture"]
fn probe_read() {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    load_eager_reader(&mut s.scheme).expect("loads");
    s.scheme.engine.set_step_limit(None);
    s.scheme.runtime_unrooted().run_word = Some(fixpt_native::cellular::run_word_registers);
    let text = fixpt_fx26::bootstrap_program();
    s.scheme.scope(|sc| {
        let pieces = sc.make(|_| Value::NULL);
        sc.scope(|inner| {
            let mut c = fixpt_fx26::Checker::new();
            let forms = c.read_in(FileId(0), &text).expect("reads");
            let done = c.declare_ahead(&forms).expect("declares");
            let tops: Vec<_> = forms.iter().zip(done).filter(|(_, d)| !d).flat_map(|(f, _)| c.top_all(f).expect("checks")).collect();
            let stage1 = inner.make(|m| {
                let mut comp = fixpt_fx26::cellular::Compiler::new(m.heap(), &c, &text);
                comp.registers = true;
                comp.program(&tops).expect("compiles")
            });
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
            eprintln!("read: {:.1} ms", 1e3 * t.elapsed().as_secs_f64());
        }
    });
}

/// The fixpoint once more, with every word of the front end compiled to
/// machine code by the compiler written in FX-26 (`native.fx`), itself
/// compiled and running on the native machine: stage 2 runs on code that
/// FX-26 made, placed by the Rust side and nothing more (step 11c).
#[test]
#[cfg_attr(debug_assertions, ignore = "seconds in release, minutes in debug: run with --release, or --ignored")]
fn fixpoint_with_words_compiled_by_fx26() {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    load_eager_reader(&mut s.scheme).expect("loads");
    s.scheme.engine.set_step_limit(None);
    s.scheme.runtime_unrooted().run_word = Some(fixpt_native::cellular::run_word_as_is);
    let text = fixpt_fx26::bootstrap_program();
    let standard: String = fixpt_fx26::standard::ENTRIES.iter().map(|(n, t)| format!("({n} {t})\n")).collect();
    let t = std::time::Instant::now();
    let lap = |what: &str| eprintln!("{what}: {:.1} s", t.elapsed().as_secs_f64());
    s.scheme.scope(|sc| {
        let facts = fixpt_fx26::syn::rust_facts(sc, FileId(0), &text).expect("checks");
        let stage1 = fixpt_fx26::syn::compile_to_word(sc, FileId(0), &text, facts).expect("parses").expect("compiles");
        let none = sc.make(|_| Value::NULL);
        let pieces = sc.call_global("%run-word", &[stage1, none]).expect("the front end runs");
        let assemble = sc.make(|m| { let p = m.get(pieces); m.heap().bloblet_slot(p, 8) });
        lap("stage 1, run: the compiler to machine code, compiled");
        // Every word stage 1 reaches, rooted.
        let mut raw = Vec::new();
        sc.make(|m| {
            let w = m.get(stage1);
            raw = reachable_words(m.heap(), w);
            Value::NULL
        });
        let words: Vec<_> = raw.into_iter().map(|w| sc.make(|_| w)).collect();
        let mut instructions = 0;
        for w in &words {
            let code = |sc: &mut fixpt_scheme::Session, far: [i64; 2]| {
                sc.scope(|one| {
                    let (ft, fe) = (one.make(|_| Value::fixnum(far[0])), one.make(|_| Value::fixnum(far[1])));
                    let args = one.call_global("list", &[*w, ft, fe]).expect("a list");
                    let r = one.call_global("%run-word", &[assemble, args]).unwrap_or_else(|e| {
                        // Which word, and how large, for a failure to say.
                        let mut shown = String::new();
                        one.make(|m| {
                            let v = m.get(*w);
                            let text = fixpt_runtime::disasm::disassemble(m.heap(), v);
                            shown = format!("{} lines: {}", text.lines().count(), text.lines().filter(|l| !l.trim().is_empty()).take(3).collect::<Vec<_>>().join(" | "));
                            Value::NULL
                        });
                        panic!("assembling {shown}: {e}")
                    });
                    one.view(|v| {
                        let r = v.get(r);
                        let ints = |l: fixpt_scheme::Local| l.list().expect("a list").iter().map(|x| x.fixnum().expect("an int")).collect::<Vec<i64>>();
                        (ints(r.field(2).expect("code")), ints(r.field(3).expect("starts")))
                    })
                })
            };
            // Once for the size, then for the place it goes.
            let (sized, _) = code(sc, [0, 0]);
            let (at, far) = fixpt_native::cellular::with_machine(|m| m.reserve(sized.len())).expect("room");
            let (words32, starts) = code(sc, far);
            assert!(words32.iter().all(|x| (0..1 << 32).contains(x)), "an instruction that could not be encoded");
            let words32: Vec<u32> = words32.into_iter().map(|x| x as u32).collect();
            instructions += words32.len();
            sc.make(|m| {
                let v = m.get(*w);
                fixpt_native::cellular::with_machine(|n| n.install(m.heap(), v, at, &words32, &starts)).expect("installs");
                Value::NULL
            });
        }
        lap(&format!("{} words, {instructions} instructions, compiled by FX-26 and placed", words.len()));
        let driver = sc.make(|m| { let p = m.get(pieces); m.heap().bloblet_slot(p, 2) });
        let (std, prog) = (sc.make(|m| m.heap().make_string(&standard)), sc.make(|m| m.heap().make_string(&text)));
        let args = sc.call_global("list", &[std, prog]).expect("a list");
        let result = sc.call_global("%run-word", &[driver, args]).expect("the driver runs");
        lap("stage 2 compiled, on machine code FX-26 made");
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

/// Every word `word` reaches through its cells and operands.
fn reachable_words(heap: &Heap, word: Value) -> Vec<Value> {
    let closure = fixpt_heap::layout::kind("cellular-closure");
    let (mut todo, mut seen, mut out) = (vec![word], std::collections::HashSet::new(), Vec::new());
    while let Some(w) = todo.pop() {
        if !seen.insert(w.raw()) {
            continue;
        }
        out.push(w);
        for k in fixpt_heap::layout::cellular::WORD_CELL0..=heap.bloblet_head(w).fields {
            let v = heap.bloblet_slot(w, k);
            if heap.is_cellular_word(v) {
                todo.push(v);
            } else if v.is_bloblet() && heap.bloblet_kind(v) == closure {
                todo.push(heap.bloblet_slot(v, fixpt_heap::layout::cellular::CLOSURE_WORD));
            }
        }
    }
    out
}

thread_local! {
    static LAST_PROFILE: std::cell::RefCell<Vec<(String, u64)>> = const { std::cell::RefCell::new(Vec::new()) };
}

/// `%run-word`'s hook, on the Rust machine, keeping a profile of the run.
fn profiled(rt: &mut fixpt_runtime::Runtime, word: Value, args: &[Value]) -> Result<Value, String> {
    let mut m = fixpt_engine::cellular::Machine::new();
    m.profile = Some(Default::default());
    m.ds.extend_from_slice(args);
    let out = m.run_in_runtime(rt, word).map_err(|t| format!("{t:?}"));
    let top = m.profile.as_ref().expect("profiling").top(usize::MAX);
    LAST_PROFILE.with(|p| *p.borrow_mut() = top);
    out?;
    m.ds.pop().ok_or_else(|| "the word left nothing".into())
}

/// Where character `at` of the bootstrap program is, as `file:line`.
fn locate_char(text: &str, at: usize) -> String {
    let parts = [
        ("eager-reader.fx", fixpt_fx26::EAGER_READER), ("parser.fx", fixpt_fx26::PARSER), ("table.fx", fixpt_fx26::TABLE),
        ("check.fx", fixpt_fx26::CHECKER), ("evaluator.fx", fixpt_fx26::EVALUATOR), ("layout.fx", fixpt_fx26::LAYOUT),
        ("standard.fx", fixpt_fx26::STANDARD_OPS), ("compile.fx", fixpt_fx26::COMPILER), ("arm64.fx", fixpt_fx26::ARM64),
        ("native-layout.fx", fixpt_fx26::NATIVE_LAYOUT), ("native.fx", fixpt_fx26::NATIVE), ("bootstrap.fx", fixpt_fx26::BOOTSTRAP),
    ];
    let byte = text.char_indices().nth(at).map_or(text.len(), |(b, _)| b);
    let mut start = 0;
    for (name, part) in parts {
        if byte < start + part.len() + 1 {
            return format!("{name}:{}", part[..(byte - start).min(part.len())].matches('\n').count() + 1);
        }
        start += part.len() + 1;
    }
    format!("char {at}")
}

/// Where the checker written in FX-26, compiled, spends its cells checking
/// the front end: by word, on the Rust machine, with each lambda named by
/// where its body starts.
#[test]
#[ignore = "a probe: cargo test --release -p fixpt-fx26 --test bootstrap probe_profile_check -- --ignored --nocapture"]
fn probe_profile_check() {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    load_eager_reader(&mut s.scheme).expect("loads");
    s.scheme.engine.set_step_limit(None);
    s.scheme.runtime_unrooted().run_word = Some(fixpt_native::cellular::run_word_as_is);
    let text = fixpt_fx26::bootstrap_program();
    let standard: String = fixpt_fx26::standard::ENTRIES.iter().map(|(n, t)| format!("({n} {t})\n")).collect();
    s.scheme.scope(|sc| {
        let facts = fixpt_fx26::syn::rust_facts(sc, FileId(0), &text).expect("checks");
        let stage1 = fixpt_fx26::syn::compile_to_word(sc, FileId(0), &text, facts).expect("parses").expect("compiles");
        let none = sc.make(|_| Value::NULL);
        let pieces = sc.call_global("%run-word", &[stage1, none]).expect("runs");
        let piece = |sc: &mut fixpt_scheme::Session, i: usize| sc.make(|m| { let p = m.get(pieces); m.heap().bloblet_slot(p, 1 + i) });
        let run = |sc: &mut fixpt_scheme::Session, f: fixpt_scheme::Handle, args: &[fixpt_scheme::Handle]| {
            let list = sc.call_global("list", args).expect("a list");
            sc.call_global("%run-word", &[f, list]).expect("runs")
        };
        let (read, parse, check) = (piece(sc, 2), piece(sc, 3), piece(sc, 4));
        let (tx, st) = (sc.make(|m| m.heap().make_string(&text)), sc.make(|m| m.heap().make_string(&standard)));
        let syns = run(sc, read, &[tx]);
        let syns = sc.make(|m| { let l = m.get(syns); m.heap().car(l) });
        let std = run(sc, read, &[st]);
        let std = sc.make(|m| { let l = m.get(std); m.heap().car(l) });
        let parsed = run(sc, parse, &[syns]);
        let tops = sc.make(|m| { let r = m.get(parsed); let p = m.heap().bloblet_slot(r, 3); m.heap().bloblet_slot(p, 2) });
        sc.runtime_unrooted().run_word = Some(profiled);
        let t = std::time::Instant::now();
        run(sc, check, &[std, tops]);
        eprintln!("checked, on the Rust machine, profiling: {:.1} s", t.elapsed().as_secs_f64());
    });
    let top = LAST_PROFILE.with(|p| p.borrow().clone());
    let total: u64 = top.iter().map(|(_, n)| n).sum();
    let in_checker: u64 = top.iter().filter(|(w, _)| w.strip_prefix("lambda@").is_some_and(|at| locate_char(&text, at.parse().unwrap_or(0)).starts_with("check.fx"))).map(|(_, n)| n).sum();
    eprintln!("{total} cells in all, {in_checker} in check.fx's code");
    for (w, n) in top.iter().take(40) {
        let at = w.strip_prefix("lambda@").and_then(|a| a.parse().ok()).map(|a| locate_char(&text, a)).unwrap_or_default();
        eprintln!("{n:>12} {:>5.1}%  {w} {at}", 100.0 * *n as f64 / total as f64);
    }
}

/// How long each phase of the front end takes on itself, run as register
/// code (as `fixpoint_as_register_code` runs it whole): read, parse, check,
/// and compile with register code.
#[test]
#[ignore = "a probe: cargo test --release -p fixpt-fx26 --test bootstrap probe_phases_as_register_code -- --ignored --nocapture"]
fn probe_phases_as_register_code() {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    load_eager_reader(&mut s.scheme).expect("loads");
    s.scheme.engine.set_step_limit(None);
    s.scheme.runtime_unrooted().run_word = Some(fixpt_native::cellular::run_word_registers);
    let text = fixpt_fx26::bootstrap_program();
    let standard: String = fixpt_fx26::standard::ENTRIES.iter().map(|(n, t)| format!("({n} {t})\n")).collect();
    let mut c = fixpt_fx26::Checker::new();
    let forms = c.read_in(FileId(0), &text).expect("reads");
    let done = c.declare_ahead(&forms).expect("declares");
    let tops: Vec<_> = forms.iter().zip(done).filter(|(_, d)| !d).flat_map(|(f, _)| c.top_all(f).expect("checks")).collect();
    s.scheme.scope(|sc| {
        let stage1 = sc.make(|m| {
            let mut comp = fixpt_fx26::cellular::Compiler::new(m.heap(), &c, &text);
            comp.registers = true;
            comp.program(&tops).expect("compiles")
        });
        let none = sc.make(|_| Value::NULL);
        let pieces = sc.call_global("%run-word", &[stage1, none]).expect("the front end runs");
        let piece = |sc: &mut fixpt_scheme::Session, i: usize| sc.make(|m| { let p = m.get(pieces); m.heap().bloblet_slot(p, 1 + i) });
        let run = |sc: &mut fixpt_scheme::Session, f: fixpt_scheme::Handle, args: &[fixpt_scheme::Handle]| {
            let list = sc.call_global("list", args).expect("a list");
            sc.call_global("%run-word", &[f, list]).expect("runs")
        };
        let (read, parse, check, compile, extracts, registers) =
            (piece(sc, 2), piece(sc, 3), piece(sc, 4), piece(sc, 5), piece(sc, 6), piece(sc, 8));
        let on = sc.make(|_| Value::TRUE);
        run(sc, registers, &[on]);
        let (tx, st) = (sc.make(|m| m.heap().make_string(&text)), sc.make(|m| m.heap().make_string(&standard)));
        let mut t = std::time::Instant::now();
        let mut gcs = (0, 0);
        let mut lap = |sc: &mut fixpt_scheme::Session, what: &str| {
            let h = &sc.runtime_unrooted().heap;
            let now = (h.gc_count, h.gc_nanos);
            eprintln!(
                "{what:>8}: {:.3} s, {} collection(s), {:.1} ms",
                t.elapsed().as_secs_f64(),
                now.0 - gcs.0,
                (now.1 - gcs.1) as f64 / 1e6
            );
            gcs = now;
            t = std::time::Instant::now();
        };
        let syns = run(sc, read, &[tx]);
        let std = run(sc, read, &[st]);
        lap(sc, "read");
        let syns = sc.make(|m| { let l = m.get(syns); m.heap().car(l) });
        let std = sc.make(|m| { let l = m.get(std); m.heap().car(l) });
        let parsed = run(sc, parse, &[syns]);
        lap(sc, "parse");
        let progs = sc.make(|m| { let r = m.get(parsed); let p = m.heap().bloblet_slot(r, 3); m.heap().bloblet_slot(p, 2) });
        run(sc, check, &[std, progs]);
        lap(sc, "check");
        let facts = run(sc, extracts, &[]);
        // With `FIXPT_PROFILE_COMPILE`, the compile on the Rust machine,
        // counting cells by word: the compiler's work, whatever its code.
        let profile = std::env::var_os("FIXPT_PROFILE_COMPILE").is_some();
        if profile {
            sc.runtime_unrooted().run_word = Some(profiled);
        }
        let _ = run(sc, compile, &[progs, facts]);
        lap(sc, "compile");
        if profile {
            let top = LAST_PROFILE.with(|p| p.borrow().clone());
            let total: u64 = top.iter().map(|(_, n)| n).sum();
            eprintln!("{total} cells");
            for (w, n) in top.iter().take(25) {
                let at = w.strip_prefix("lambda@").and_then(|a| a.parse().ok()).map(|a| locate_char(&text, a)).unwrap_or_default();
                eprintln!("{n:>12}  {w} {at}");
            }
        }
    });
}
