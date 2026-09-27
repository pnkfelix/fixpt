//! The compiler to threaded words written in Rust (`src/threaded.rs`)
//! against the one written in FX-26 (`src/compile.fx`): the same words,
//! cell for cell, for every test program and for the whole bootstrap
//! program; and the Rust one's words run as the lowering does (PLAN.md,
//! M13 step 13a).

use fixpt_engine::Backend;
use fixpt_fx26::session::{Fx26Session, load_eager_reader};
use fixpt_fx26::{Checker, Top};
use fixpt_heap::Value;
use fixpt_read::FileId;
use std::collections::HashMap;

mod common;
use common::same_code;

thread_local! {
    /// Register words compared, in all.
    static REGISTER_WORDS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// The Rust checker's forms for `text`, and the checker, or why not.
fn checked(text: &str) -> Result<(Checker, Vec<Top>), String> {
    let mut c = Checker::new();
    let forms = c.read_in(FileId(0), text).map_err(|e| e.message)?;
    let done = c.declare_ahead(&forms).map_err(|e| e.message)?;
    let mut tops = Vec::new();
    for (f, done) in forms.iter().zip(done) {
        if !done {
            tops.push(c.top(f).map_err(|e| e.message)?);
        }
    }
    Ok((c, tops))
}

/// Both compilers on `text`, in one session: whether they made the same
/// words, or what differs. `None` if the program does not check.
fn compare(s: &mut Fx26Session, text: &str) -> Option<Result<(), String>> {
    compare_with(s, text, false)
}

/// The same, with `registers`: each lambda's register code, its word's twin,
/// made by both compilers' register compilers and compared too.
fn compare_with(s: &mut Fx26Session, text: &str, registers: bool) -> Option<Result<(), String>> {
    let (c, tops) = checked(text).ok()?;
    Some(s.scheme.scope(|sc| {
        let facts = fixpt_fx26::syn::rust_facts(sc, FileId(0), text).map_err(|e| e.message)?;
        let theirs = if registers {
            fixpt_fx26::syn::compile_to_word_with_registers(sc, FileId(0), text, facts)
        } else {
            fixpt_fx26::syn::compile_to_word(sc, FileId(0), text, facts)
        }
        .map_err(|e| e.message)?;
        let mut ours_err = None;
        let ours = sc.make(|m| {
            let mut comp = fixpt_fx26::threaded::Compiler::new(m.heap(), &c, text);
            comp.registers = registers;
            match comp.program(&tops) {
                Ok(w) => w,
                Err(e) => {
                    ours_err = Some(e);
                    Value::NULL
                }
            }
        });
        match (theirs, ours_err) {
            (Err(t), Some(o)) if t == o => Ok(()),
            (Err(t), o) => Err(format!("FX-26: {t}; Rust: {o:?}")),
            (Ok(_), Some(o)) => Err(format!("the Rust compiler: {o}")),
            (Ok(theirs), None) => {
                let (mut same, mut why) = (false, String::new());
                sc.make(|m| {
                    let (a, b) = (m.get(theirs), m.get(ours));
                    same = same_code(m.heap(), a, b, &mut HashMap::new(), &mut why);
                    if same && registers {
                        let fx = common::register_words(m.heap(), a, &mut Default::default());
                        let rust = common::register_words(m.heap(), b, &mut Default::default());
                        REGISTER_WORDS.with(|n| n.set(n.get() + fx));
                        assert_eq!(fx, rust, "as many register words");
                    }
                    Value::NULL
                });
                if same { Ok(()) } else { Err(why) }
            }
        }
    }))
}

fn programs() -> Vec<(String, String)> {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs");
    let mut out = Vec::new();
    for sub in ["bidirectional", "bloblet", "control", "run", "pldi89"] {
        let mut names: Vec<_> = std::fs::read_dir(format!("{dir}/{sub}")).unwrap().map(|e| e.unwrap().path()).collect();
        names.sort();
        for p in names {
            out.push((format!("{sub}/{}", p.file_name().unwrap().to_string_lossy()), std::fs::read_to_string(&p).unwrap()));
        }
    }
    out
}

#[test]
fn every_test_program_compiles_the_same() {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    load_eager_reader(&mut s.scheme).expect("loads");
    s.scheme.engine.set_step_limit(None);
    let (mut report, mut same) = (Vec::new(), 0);
    for (name, text) in programs() {
        match compare(&mut s, &text) {
            None => {}
            Some(Ok(())) => same += 1,
            Some(Err(why)) => report.push(format!("{name}: {why}")),
        }
    }
    eprintln!("{same} programs compile the same");
    assert!(report.is_empty(), "{}", report.join("\n"));
    assert!(same >= 15, "only {same}");
}

/// The same, with register code: the register compiler written in FX-26
/// (`regcode.fx`) makes each lambda's twin as the Rust one does.
#[test]
fn every_test_program_has_the_same_register_code() {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    load_eager_reader(&mut s.scheme).expect("loads");
    s.scheme.engine.set_step_limit(None);
    let (mut report, mut same) = (Vec::new(), 0);
    for (name, text) in programs() {
        match compare_with(&mut s, &text, true) {
            None => {}
            Some(Ok(())) => same += 1,
            Some(Err(why)) => report.push(format!("{name}: {why}")),
        }
    }
    let words = REGISTER_WORDS.with(|n| n.get());
    eprintln!("{same} programs have the same register code, {words} register words in all");
    assert!(report.is_empty(), "{}", report.join("\n"));
    assert!(same >= 15, "only {same}");
    assert!(words >= 50, "only {words} register words were compared");
}

/// The Rust compiler's words, run on the Rust machine, as the lowering runs
/// the program.
#[test]
fn the_rust_compilers_words_run_as_lowered() {
    let mut report = Vec::new();
    let mut ran = 0;
    for (name, text) in programs() {
        let Ok((c, tops)) = checked(&text) else { continue };
        let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
        let Ok(Ok(lowered)) = s.run_program(&text).map(|v| v.map_err(|e| e.to_string())) else { continue };
        let got = s.scheme.scope(|sc| {
            let mut err = None;
            let w = sc.make(|m| match fixpt_fx26::threaded::Compiler::new(m.heap(), &c, &text).program(&tops) {
                Ok(w) => w,
                Err(e) => {
                    err = Some(e);
                    Value::NULL
                }
            });
            if let Some(e) = err {
                return format!("!! {e}");
            }
            let none = sc.make(|_| Value::NULL);
            match sc.call_global("%run-word", &[w, none]) {
                Ok(v) => sc.write(v),
                Err(e) => format!("!! {e}"),
            }
        });
        ran += 1;
        let norm = |v: &str| if v.is_empty() || v == "#u" { "#u".to_string() } else { v.to_string() };
        if norm(&got) != norm(&lowered) {
            report.push(format!("{name}: Rust-compiled {got:?}, lowered {lowered:?}"));
        }
    }
    assert!(report.is_empty(), "{}", report.join("\n"));
    assert!(ran >= 15, "only {ran}");
}

/// The whole bootstrap program: every word the same.
#[test]
#[cfg_attr(debug_assertions, ignore = "seconds in release: run with --release")]
fn the_bootstrap_program_compiles_the_same() {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    load_eager_reader(&mut s.scheme).expect("loads");
    s.scheme.engine.set_step_limit(None);
    let text = fixpt_fx26::bootstrap_program();
    assert_eq!(compare(&mut s, &text), Some(Ok(())));
}
