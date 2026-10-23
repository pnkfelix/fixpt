//! Typed cellular code (`docs/research/typed-cellular-code.md`): the Rust
//! compiler's words, each with its certificate, verified against it, over
//! every test program.

use fixpt_engine::Backend;
use fixpt_fx26::session::Fx26Session;
use fixpt_fx26::typed_cells::{verify, Certs};
use fixpt_fx26::{Checker, Top};
use fixpt_heap::Value;
use fixpt_read::FileId;
use std::collections::BTreeMap;

fn modules_dir() -> std::path::PathBuf {
    std::path::PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs/modules"))
}

/// The Rust checker's forms for `text`, its types kept, or why not.
fn checked(text: &str) -> Result<(Checker, Vec<Top>), String> {
    let mut c = Checker::new();
    c.base_dir = Some(modules_dir());
    c.record_types = true;
    let forms = c.read_in(FileId(0), text).map_err(|e| e.message)?;
    let done = c.declare_ahead(&forms).map_err(|e| e.message)?;
    let mut tops = Vec::new();
    for (f, done) in forms.iter().zip(done) {
        if !done {
            tops.extend(c.top_all(f).map_err(|e| e.message)?);
        }
    }
    Ok((c, tops))
}

/// What verifying a program's words found.
#[derive(Default)]
struct Tally {
    words: usize,
    verified: usize,
    discharged: usize,
    stopped: BTreeMap<String, usize>,
    open: usize,
    failed: Vec<String>,
    open_examples: Vec<String>,
}

fn verify_program(s: &mut Fx26Session, name: &str, text: &str, t: &mut Tally) {
    let Ok((mut c, tops)) = checked(text) else { return };
    fixpt_fx26::syn::set_load_base(Some(modules_dir()));
    s.scheme.scope(|sc| {
        sc.make(|m| {
            let certs = {
                let mut comp = fixpt_fx26::cellular::Compiler::new(m.heap(), &c, text);
                comp.certs = Some(Certs::default());
                if comp.program(&tops).is_err() {
                    return Value::NULL;
                }
                comp.certs.take().expect("made")
            };
            let mut certs = certs;
            if let Err(why) = certs.settle(&c) {
                t.failed.push(format!("{name}: {why}"));
            }
            let heap: &fixpt_heap::Heap = m.heap();
            for raw in certs.words.keys() {
                let o = verify(&mut c, heap, &certs, Value::from_raw(*raw));
                t.words += 1;
                t.discharged += o.discharged;
                t.verified += o.verified() as usize;
                if let Some(why) = &o.stopped {
                    *t.stopped.entry(why.clone()).or_default() += 1;
                }
                t.open += o.open.len();
                if t.open_examples.len() < 12 {
                    t.open_examples.extend(o.open.iter().take(1).map(|x| format!("{name}: {x}")));
                }
                t.failed.extend(o.failed.iter().map(|f| format!("{name}: {f}")));
            }
            Value::NULL
        });
    });
}

/// Each word of `text` that verifies, mutated one way at a time where it
/// can be: an `int-add` made a `pair-car` (an int taken for a pair), and a
/// `pair-car` made an `int-add` (a pair added). Each mutant must be refused.
/// Returns how many mutants were made, and those not refused.
fn mutants(s: &mut Fx26Session, name: &str, text: &str) -> (usize, Vec<String>) {
    use fixpt_heap::layout::cellular::{operands, routine, ROUTINES, PRIMITIVES, WORD_CELL0};
    let Ok((mut c, tops)) = checked(text) else { return (0, Vec::new()) };
    fixpt_fx26::syn::set_load_base(Some(modules_dir()));
    let (mut made, mut kept) = (0, Vec::new());
    s.scheme.scope(|sc| {
        sc.make(|m| {
            let certs = {
                let mut comp = fixpt_fx26::cellular::Compiler::new(m.heap(), &c, text);
                comp.certs = Some(Certs::default());
                if comp.program(&tops).is_err() {
                    return Value::NULL;
                }
                comp.certs.take().expect("made")
            };
            let mut certs = certs;
            certs.settle(&c).expect("settled");
            for raw in certs.words.keys() {
                let w = Value::from_raw(*raw);
                if !verify(&mut c, m.heap(), &certs, w).verified() {
                    continue;
                }
                // Each instruction's cell, operands skipped.
                let n = m.heap().bloblet_head(w).fields;
                let mut k = WORD_CELL0;
                while k <= n {
                    let cell = m.heap().bloblet_slot(w, k);
                    let r = cell.is_fixnum().then(|| cell.as_fixnum() as usize).filter(|r| *r < PRIMITIVES).map(|r| ROUTINES[r].0);
                    let swap = match r {
                        Some("int-add") => Some("pair-car"),
                        Some("pair-car") => Some("int-add"),
                        _ => None,
                    };
                    if let Some(to) = swap {
                        m.heap().set_bloblet_slot(w, k, Value::fixnum(routine(to) as i64));
                        made += 1;
                        let o = verify(&mut c, m.heap(), &certs, w);
                        if o.verified() || o.failed.is_empty() && o.stopped.is_none() {
                            kept.push(format!("{name}: {} at cell {} made {to}", r.unwrap_or("?"), k - WORD_CELL0));
                        }
                        m.heap().set_bloblet_slot(w, k, cell);
                    }
                    k += 1 + r.map_or(0, operands);
                }
            }
            Value::NULL
        });
    });
    (made, kept)
}

/// A verified word changed is refused: the verifier is not merely
/// agreeing with the compiler (directions §4, C5's mutation tests).
#[test]
fn a_verified_word_changed_is_refused() {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    let (mut made, mut kept) = (0, Vec::new());
    for (name, text) in programs() {
        let (m, k) = mutants(&mut s, &name, &text);
        made += m;
        kept.extend(k);
    }
    eprintln!("{made} mutants, {} not refused", kept.len());
    assert!(made > 20, "too few mutants: {made}");
    assert!(kept.is_empty(), "mutants verified:\n{}", kept.join("\n"));
}

/// The test programs some of whose type VCs fail, and how many: each a
/// rule the verifier does not have yet (`TODO.md` §115), not a fault of
/// the checker's or the compiler's. A failure in a program not here, or
/// more than its count, fails the test; fewer is to be written here.
/// Their causes: placeholders (`letrec`, `define-rec`, a forward
/// definition: `#f` where a value goes until patched); a functor's
/// `(select $1 t)`; nested `poly`s and a place's binders; regions frozen
/// or certified (`letfreeze`, `acyclic`); a natural after a test (size
/// facts); `datum` and a union by a type test; `car` of `nil`, which is
/// certain to fail, in a program that means to (`fails-car.fx`).
const KNOWN_FAILURES: &[(&str, usize)] = &[
    ("bidirectional/arrow.fx", 1),
    ("bidirectional/arrow-star-groups.fx", 7),
    ("bidirectional/arrow-star-module.fx", 3),
    ("bidirectional/bounds.fx", 1),
    ("bidirectional/twice.fx", 1),
    ("bloblet/array-sum.fx", 1),
    ("bloblet/flat-bounds.fx", 1),
    ("bloblet/flat-unsized.fx", 2),
    ("datum/acyclic.fx", 3),
    ("datum/confirm-length.fx", 2),
    ("datum/quasiquote.fx", 2),
    ("datum/quote.fx", 2),
    ("datum/quote-identity.fx", 1),
    ("datum/quote-shadowed.fx", 2),
    ("datum/type-tests.fx", 1),
    ("datum/union.fx", 2),
    ("modules/forward.fx", 1),
    ("modules/functor-abstract.fx", 2),
    ("modules/functor-max.fx", 2),
    ("modules/include-param-shadows.fx", 1),
    ("modules/linked.fx", 1),
    ("modules/load-parameters.fx", 1),
    ("modules/mutual.fx", 1),
    ("modules/own-name.fx", 1),
    ("modules/rec.fx", 1),
    ("modules/star-self.fx", 1),
    ("run/acyclic-in-a-place.fx", 1),
    ("run/acyclic-lists.fx", 2),
    ("run/fails-car.fx", 1),
    ("run/generative.fx", 1),
    ("run/icells.fx", 4),
    ("run/letfreeze.fx", 1),
    ("run/loops.fx", 1),
    ("run/region-allocators.fx", 4),
    ("run/variadic.fx", 1),
    ("run/well-founded.fx", 2),
];

fn programs() -> Vec<(String, String)> {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs");
    let mut out = Vec::new();
    for sub in ["bidirectional", "bloblet", "control", "run", "pldi89", "datum", "modules"] {
        let mut names: Vec<_> = std::fs::read_dir(format!("{dir}/{sub}")).unwrap().map(|e| e.unwrap().path()).collect();
        names.sort();
        for p in names {
            out.push((format!("{sub}/{}", p.file_name().unwrap().to_string_lossy()), std::fs::read_to_string(&p).unwrap()));
        }
    }
    out
}

/// Every word of every test program, verified: how many verify, where the
/// verifier stops for want of a rule, and which VCs it leaves open. None
/// may fail: the checker accepted these programs, so a failure is the
/// verifier's mistake or the compiler's.
#[test]
fn every_test_programs_words_verified() {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    let mut t = Tally::default();
    for (name, text) in programs() {
        verify_program(&mut s, &name, &text, &mut t);
    }
    eprintln!("{} words: {} verified, {} VCs discharged, {} open", t.words, t.verified, t.discharged, t.open);
    for (why, n) in &t.stopped {
        eprintln!("  stopped {n:5}: {why}");
    }
    for o in &t.open_examples {
        eprintln!("  open: {o}");
    }
    for f in t.failed.iter().take(if std::env::var_os("ALL").is_some() { usize::MAX } else { 30 }) {
        eprintln!("  FAILED {f}");
    }
    // A ratchet: what verifies now, as the verifier grows; and no failure
    // outside those the verifier's missing rules explain.
    assert!(t.verified >= 629, "fewer words verify: {}", t.verified);
    let mut by: BTreeMap<&str, usize> = BTreeMap::new();
    for f in &t.failed {
        *by.entry(f.split(':').next().unwrap_or("")).or_default() += 1;
    }
    let known: BTreeMap<&str, usize> = KNOWN_FAILURES.iter().copied().collect();
    let worse: Vec<String> = by.iter().filter(|(p, n)| **n > known.get(*p).copied().unwrap_or(0)).map(|(p, n)| format!("{p}: {n}")).collect();
    let better: Vec<String> = known.iter().filter(|(p, n)| by.get(*p).copied().unwrap_or(0) < **n).map(|(p, n)| format!("{p}: {} (was {n})", by.get(*p).copied().unwrap_or(0))).collect();
    if !better.is_empty() {
        eprintln!("fewer failures than KNOWN_FAILURES says, to write there: {better:?}");
    }
    assert!(worse.is_empty(), "type VCs failing beyond those known: {worse:?}");
}
