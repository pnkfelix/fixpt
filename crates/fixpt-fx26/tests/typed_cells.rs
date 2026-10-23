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
    assumed: usize,
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
            if let Err(why) = certs.settle(&mut c) {
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
                    if std::env::var("WHY").is_ok_and(|w| why.contains(&w)) {
                        eprintln!("  STOP {name}: {why}");
                    }
                }
                t.open += o.open.len();
                t.assumed += o.assumed.len();
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
/// can be, each routine `swaps` names made the other it names (an
/// `int-add` made a `pair-car`, an int taken for a pair). Each mutant must
/// be refused: a VC failed or, with `open` refusing (of a word with a
/// specification), left open.
/// Returns how many mutants were made, and those not refused.
fn mutants(s: &mut Fx26Session, name: &str, text: &str, swaps: &[(&str, &str)], open: bool) -> (usize, Vec<String>) {
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
            certs.settle(&mut c).expect("settled");
            for raw in certs.words.keys() {
                let w = Value::from_raw(*raw);
                // (With `open`, only a specified word: another promises
                // nothing its arithmetic could break.)
                if !verify(&mut c, m.heap(), &certs, w).verified() || open && certs.words[raw].spec.is_none() {
                    continue;
                }
                // Each instruction's cell, operands skipped.
                let n = m.heap().bloblet_head(w).fields;
                let mut k = WORD_CELL0;
                while k <= n {
                    let cell = m.heap().bloblet_slot(w, k);
                    let r = cell.is_fixnum().then(|| cell.as_fixnum() as usize).filter(|r| *r < PRIMITIVES).map(|r| ROUTINES[r].0);
                    let swap = swaps.iter().find(|(from, _)| r == Some(*from)).map(|(_, to)| *to);
                    if let Some(to) = swap {
                        m.heap().set_bloblet_slot(w, k, Value::fixnum(routine(to) as i64));
                        made += 1;
                        let o = verify(&mut c, m.heap(), &certs, w);
                        if o.verified() || o.failed.is_empty() && o.stopped.is_none() && !(open && !o.open.is_empty()) {
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
        let (m, k) = mutants(&mut s, &name, &text, &[("int-add", "pair-car"), ("pair-car", "int-add")], false);
        made += m;
        kept.extend(k);
    }
    eprintln!("{made} mutants, {} not refused", kept.len());
    assert!(made > 20, "too few mutants: {made}");
    assert!(kept.is_empty(), "mutants verified:\n{}", kept.join("\n"));
}

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

/// Every word of every test program, verified: each must verify. The
/// checker accepted these programs, so a VC that fails is the verifier's
/// mistake or the compiler's; one left open, or a word the verifier stops
/// in, a rule it lacks. What is assumed (the scheduler's procedures at
/// their forms' types) is said, not refused.
#[test]
fn every_test_programs_words_verified() {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    let mut t = Tally::default();
    for (name, text) in programs() {
        verify_program(&mut s, &name, &text, &mut t);
    }
    eprintln!("{} words: {} verified, {} VCs discharged, {} open, {} assumed", t.words, t.verified, t.discharged, t.open, t.assumed);
    for (why, n) in &t.stopped {
        eprintln!("  stopped {n:5}: {why}");
    }
    for o in &t.open_examples {
        eprintln!("  open: {o}");
    }
    for f in t.failed.iter().take(if std::env::var_os("ALL").is_some() { usize::MAX } else { 30 }) {
        eprintln!("  FAILED {f}");
    }
    // Every word, every VC discharged: none failing, none left open, and
    // no word the verifier stops in for want of a rule.
    assert!(t.failed.is_empty(), "type VCs failed: {}", t.failed.len());
    assert!(t.open == 0, "VCs left open: {}", t.open);
    assert!(t.stopped.is_empty(), "words stopped in: {:?}", t.stopped);
    assert!(t.verified == t.words && t.words > 1000, "{} of {} words verified", t.verified, t.words);
}

/// Programs that state propositions (`requires`, `ensures`; the note's
/// §8): each says on its first line whether its words verify. One marked
/// `; Verified` must, every VC discharged; one marked `; Unverified` must
/// leave a VC open (a proposition the prover cannot show, which is what a
/// false one is to it), and fail none of its types; one marked `; Refused`
/// the checker refuses (a specification not within another, or not well
/// formed).
#[test]
fn specifications_as_they_say() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs/specs");
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    let mut names: Vec<_> = std::fs::read_dir(dir).unwrap().map(|e| e.unwrap().path()).collect();
    names.sort();
    let mut wrong = Vec::new();
    for p in names {
        let text = std::fs::read_to_string(&p).unwrap();
        let name = format!("specs/{}", p.file_name().unwrap().to_string_lossy());
        let mut t = Tally::default();
        t.open_examples.clear();
        verify_program(&mut s, &name, &text, &mut t);
        let said = text.lines().next().unwrap_or("");
        let ok = match said {
            "; Refused" => checked(&text).is_err(),
            "; Verified" => t.verified == t.words && t.words > 0,
            "; Unverified" => t.failed.is_empty() && t.stopped.is_empty() && t.open > 0,
            _ => false,
        };
        eprintln!("{name}: {} of {} words verified, {} VCs discharged, {} open", t.verified, t.words, t.discharged, t.open);
        for o in &t.open_examples {
            eprintln!("  open: {o}");
        }
        for f in &t.failed {
            eprintln!("  FAILED {f}");
        }
        for (why, n) in &t.stopped {
            eprintln!("  stopped {n}: {why}");
        }
        if !ok {
            wrong.push(name);
        }
    }
    assert!(wrong.is_empty(), "not as their first line says: {wrong:?}");
}

/// A word that verifies against its specification, its arithmetic
/// changed (an `int-add` made an `int-sub`, and the reverse), is refused:
/// what it ensures is not shown of what it now computes. (Correctness is
/// partial: a loop made endless still ensures what it would if it ended,
/// so the specifications here say exactly what is computed.)
#[test]
fn a_specified_word_changed_is_refused() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs/specs");
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    let (mut made, mut kept) = (0, Vec::new());
    let mut names: Vec<_> = std::fs::read_dir(dir).unwrap().map(|e| e.unwrap().path()).collect();
    names.sort();
    for p in names {
        let text = std::fs::read_to_string(&p).unwrap();
        let name = format!("specs/{}", p.file_name().unwrap().to_string_lossy());
        let (m, k) = mutants(&mut s, &name, &text, &[("int-add", "int-sub"), ("int-sub", "int-add")], true);
        made += m;
        kept.extend(k);
    }
    eprintln!("{made} mutants, {} not refused", kept.len());
    assert!(made >= 5, "too few mutants: {made}");
    assert!(kept.is_empty(), "mutants verified:\n{}", kept.join("\n"));
}
