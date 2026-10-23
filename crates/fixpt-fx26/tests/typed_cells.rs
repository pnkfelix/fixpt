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

/// The directory a test program named `sub/file.fx` loads files from: its
/// own.
fn base_of(name: &str) -> std::path::PathBuf {
    let sub = name.split('/').next().unwrap_or("modules");
    std::path::PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs")).join(sub)
}

/// The Rust checker's forms for `text`, its types kept, or why not.
fn checked(text: &str) -> Result<(Checker, Vec<Top>), String> {
    checked_in(text, modules_dir())
}

/// The same, `text` loading files from `base`.
fn checked_in(text: &str, base: std::path::PathBuf) -> Result<(Checker, Vec<Top>), String> {
    let mut c = Checker::new();
    c.base_dir = Some(base);
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
    /// Programs the checker refused, and those the compiler did not
    /// compile, whose words were not verified.
    refused: usize,
    uncompiled: usize,
    /// The words not verified, `program `word``; what of the open VCs and
    /// stops is theirs, of `KNOWN_GAPS`.
    unverified: Vec<String>,
    open_gaps: usize,
    stopped_gaps: Vec<String>,
    /// Time spent checking, compiling (with certificates), and verifying.
    check_time: std::time::Duration,
    compile_time: std::time::Duration,
    verify_time: std::time::Duration,
}

fn verify_program(s: &mut Fx26Session, name: &str, text: &str, t: &mut Tally) {
    use std::time::Instant;
    let start = Instant::now();
    let checked = checked_in(text, base_of(name));
    t.check_time += start.elapsed();
    let Ok((mut c, tops)) = checked else {
        t.refused += 1;
        return;
    };
    fixpt_fx26::syn::set_load_base(Some(base_of(name)));
    s.scheme.scope(|sc| {
        sc.make(|m| {
            let start = Instant::now();
            let certs = {
                let mut comp = fixpt_fx26::cellular::Compiler::new(m.heap(), &c, text);
                comp.certs = Some(Certs::default());
                if comp.program(&tops).is_err() {
                    t.uncompiled += 1;
                    t.compile_time += start.elapsed();
                    return Value::NULL;
                }
                comp.certs.take().expect("made")
            };
            t.compile_time += start.elapsed();
            let start = Instant::now();
            let mut certs = certs;
            if let Err(why) = certs.settle(&mut c) {
                t.failed.push(format!("{name}: {why}"));
            }
            let heap: &fixpt_heap::Heap = m.heap();
            for raw in certs.words.keys() {
                let o = verify(&mut c, heap, &certs, Value::from_raw(*raw));
                // The word, by its name, in what is said of it.
                let named = heap.bloblet_slot(Value::from_raw(*raw), fixpt_heap::layout::cellular::WORD_NAME);
                let word = if heap.is_a(named, fixpt_heap::ObjType::Symbol) { heap.symbol_name(named).to_string() } else { "?".into() };
                let name = &format!("{name} `{word}`");
                if !o.verified() {
                    t.unverified.push(name.clone());
                    if KNOWN_GAPS.contains(&name.as_str()) {
                        t.open_gaps += o.open.len();
                        t.stopped_gaps.extend(o.stopped.clone());
                    }
                }
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
            t.verify_time += start.elapsed();
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
    let Ok((mut c, tops)) = checked_in(text, base_of(name)) else { return (0, Vec::new()) };
    fixpt_fx26::syn::set_load_base(Some(base_of(name)));
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

/// Each verified word's latent effect made smaller by one atom, in turn:
/// how many were, those that still verified, and those that verified only
/// for the masked expressions' cells (`Cert::masks`) the certificate
/// marks, which would be the verifier masking more than the checker did.
fn weakened(s: &mut Fx26Session, name: &str, text: &str) -> (usize, Vec<String>, Vec<String>) {
    let Ok((mut c, tops)) = checked_in(text, base_of(name)) else { return (0, Vec::new(), Vec::new()) };
    fixpt_fx26::syn::set_load_base(Some(base_of(name)));
    let (mut made, mut kept, mut by_masks) = (0, Vec::new(), Vec::new());
    s.scheme.scope(|sc| {
        sc.make(|m| {
            let mut certs = {
                let mut comp = fixpt_fx26::cellular::Compiler::new(m.heap(), &c, text);
                comp.certs = Some(Certs::default());
                if comp.program(&tops).is_err() {
                    return Value::NULL;
                }
                comp.certs.take().expect("made")
            };
            certs.settle(&mut c).expect("settled");
            let words: Vec<u64> = certs.words.keys().copied().collect();
            for raw in words {
                let w = Value::from_raw(raw);
                let Some(latent) = certs.words[&raw].effect.clone() else { continue };
                if !verify(&mut c, m.heap(), &certs, w).verified() {
                    continue;
                }
                for a in latent.0.iter() {
                    let mut less = latent.clone();
                    less.0.remove(a);
                    // Still said by the rest (`(read @globals)` says every
                    // global's read): no weaker.
                    if fixpt_fx26::ast::Effect(std::iter::once(*a).collect()).within(&less) {
                        continue;
                    }
                    certs.words.get_mut(&raw).expect("there").effect = Some(less);
                    made += 1;
                    if verify(&mut c, m.heap(), &certs, w).verified() {
                        let what = format!("{name}: {a:?} of {}", c.show_effect(&latent));
                        let masks = std::mem::take(&mut certs.words.get_mut(&raw).expect("there").masks);
                        if !verify(&mut c, m.heap(), &certs, w).verified() {
                            by_masks.push(what.clone());
                        }
                        certs.words.get_mut(&raw).expect("there").masks = masks;
                        kept.push(what);
                    }
                }
                certs.words.get_mut(&raw).expect("there").effect = Some(latent);
            }
            Value::NULL
        });
    });
    (made, kept, by_masks)
}

/// A latent effect made smaller is not verified for what the verifier
/// masks of expressions inside a word: it masks no more than the checker,
/// whose latent effect keeps only what its masking did not drop; and a
/// global's read is never left out unseen. (Some still verify, for what
/// the verifier does not yet compute: `spin`, and what the scheduler's
/// procedures, trusted at their forms' types, do to its private regions;
/// `TODO.md` §117. `ALL` lists them.)
#[test]
fn a_latent_effect_weakened_is_not_masked_away() {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    let (mut made, mut kept, mut by_masks) = (0, Vec::new(), Vec::new());
    for (name, text) in programs() {
        let (m, k, b) = weakened(&mut s, &name, &text);
        made += m;
        kept.extend(k);
        by_masks.extend(b);
    }
    eprintln!("{made} latent effects weakened, {} verified still, {} for the masks alone", kept.len(), by_masks.len());
    if std::env::var_os("ALL").is_some() {
        for k in &kept {
            eprintln!("  {k}");
        }
    }
    assert!(made > 10000, "too few weakened: {made}");
    assert!(by_masks.is_empty(), "weakened, and verified for the masks alone:\n{}", by_masks.join("\n"));
    let reads: Vec<&String> = kept.iter().filter(|k| k.contains(": Read(Global(")).collect();
    assert!(reads.is_empty(), "a global's read left out, and verified:\n{reads:?}");
}

/// Every test program, by directory, but `specs`, whose programs say
/// whether they verify (`specifications_as_they_say`).
fn programs() -> Vec<(String, String)> {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs");
    let mut subs: Vec<String> = std::fs::read_dir(dir).unwrap().map(|e| e.unwrap()).filter(|e| e.path().is_dir()).map(|e| e.file_name().to_string_lossy().into_owned()).collect();
    subs.sort();
    let mut out = Vec::new();
    for sub in subs.iter().filter(|d| *d != "specs") {
        let mut names: Vec<_> = std::fs::read_dir(format!("{dir}/{sub}")).unwrap().map(|e| e.unwrap().path()).filter(|p| p.extension().is_some_and(|x| x == "fx")).collect();
        names.sort();
        for p in names {
            out.push((format!("{sub}/{}", p.file_name().unwrap().to_string_lossy()), std::fs::read_to_string(&p).unwrap()));
        }
    }
    out
}

/// Every directory of test programs, verified, a survey: per directory,
/// what verified, stopped, failed or was left open, and the time each
/// phase took; then the programs slowest to verify. Ignored by default;
/// `DIRS=a,b` limits it to some, and `FILES=p,q` verifies those files
/// instead, each word's failures in full.
#[test]
#[ignore]
fn every_directory_surveyed() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs");
    let only: Option<Vec<String>> = std::env::var("DIRS").ok().map(|d| d.split(',').map(String::from).collect());
    let mut subs: Vec<String> = std::fs::read_dir(dir).unwrap().map(|e| e.unwrap()).filter(|e| e.path().is_dir()).map(|e| e.file_name().to_string_lossy().into_owned()).collect();
    subs.sort();
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    if let Ok(files) = std::env::var("FILES") {
        for f in files.split(',') {
            let mut t = Tally::default();
            verify_program(&mut s, &format!("modules/{f}"), &std::fs::read_to_string(f).unwrap(), &mut t);
            eprintln!("{f}: {} of {} words verified, {} open, refused {}", t.verified, t.words, t.open, t.refused);
            for x in t.failed.iter().chain(&t.open_examples).chain(t.stopped.keys()) {
                eprintln!("  {x}");
            }
        }
        return;
    }
    let mut slow: Vec<(std::time::Duration, std::time::Duration, std::time::Duration, String, usize)> = Vec::new();
    let mut all = Tally::default();
    for sub in subs.iter().filter(|d| only.as_ref().is_none_or(|o| o.contains(d))) {
        let mut names: Vec<_> = std::fs::read_dir(format!("{dir}/{sub}")).unwrap().map(|e| e.unwrap().path()).filter(|p| p.extension().is_some_and(|x| x == "fx")).collect();
        names.sort();
        let mut t = Tally::default();
        for p in &names {
            let name = format!("{sub}/{}", p.file_name().unwrap().to_string_lossy());
            let text = std::fs::read_to_string(p).unwrap();
            let mut one = Tally::default();
            verify_program(&mut s, &name, &text, &mut one);
            // A refusal the program does not say it expects: the harness's,
            // or the checker's own.
            if one.refused > 0 && !text.starts_with("; Rejected") && !text.starts_with("; Refused") {
                eprintln!("  refused, unexpectedly: {name}: {}", checked_in(&text, base_of(&name)).err().unwrap_or_default().lines().next().unwrap_or(""));
            }
            slow.push((one.verify_time, one.compile_time, one.check_time, name, one.words));
            t.words += one.words;
            t.verified += one.verified;
            t.discharged += one.discharged;
            t.open += one.open;
            t.assumed += one.assumed;
            t.refused += one.refused;
            t.uncompiled += one.uncompiled;
            t.check_time += one.check_time;
            t.compile_time += one.compile_time;
            t.verify_time += one.verify_time;
            for (why, n) in one.stopped {
                *t.stopped.entry(why).or_default() += n;
            }
            t.failed.extend(one.failed);
            t.open_examples.extend(one.open_examples.into_iter().take(1));
        }
        eprintln!(
            "{sub}: {} programs ({} refused, {} not compiled); {} words, {} verified, {} open, {} failed, {} stopped; check {:.2}s, compile {:.2}s, verify {:.2}s",
            names.len(),
            t.refused,
            t.uncompiled,
            t.words,
            t.verified,
            t.open,
            t.failed.len(),
            t.stopped.values().sum::<usize>(),
            t.check_time.as_secs_f64(),
            t.compile_time.as_secs_f64(),
            t.verify_time.as_secs_f64()
        );
        for (why, n) in &t.stopped {
            eprintln!("  stopped {n:5}: {why}");
        }
        for o in t.open_examples.iter().take(3) {
            eprintln!("  open: {o}");
        }
        for f in t.failed.iter().take(5) {
            eprintln!("  FAILED {f}");
        }
        all.words += t.words;
        all.verified += t.verified;
        all.check_time += t.check_time;
        all.compile_time += t.compile_time;
        all.verify_time += t.verify_time;
    }
    eprintln!("all: {} words, {} verified; check {:.2}s, compile {:.2}s, verify {:.2}s", all.words, all.verified, all.check_time.as_secs_f64(), all.compile_time.as_secs_f64(), all.verify_time.as_secs_f64());
    slow.sort_by(|a, b| b.0.cmp(&a.0));
    for (v, c, k, name, words) in slow.iter().take(15) {
        eprintln!("  slowest: {name}: verify {:.3}s ({words} words), compile {:.3}s, check {:.3}s", v.as_secs_f64(), c.as_secs_f64(), k.as_secs_f64());
    }
}

/// The words not yet verified, each a rule the certificate does not yet
/// carry what it needs for (`TODO.md` §117): a prompt's own transfers of
/// control that the checker drops where nothing but its tag's variable
/// reaches the tag (`given`); a global redefined at another type, which
/// the certificate gives one type (`f` and `h`, and the program's own
/// word).
const KNOWN_GAPS: &[&str] = &[
    "native/raw-args.fx `given`",
    "redefine/knot-spin.fx `f`",
    "redefine/knot-spin.fx `h`",
    "redefine/rerun-chain.fx `program`",
];

/// Every word of every test program, verified: each must verify. The
/// checker accepted these programs, so a VC that fails is the verifier's
/// mistake or the compiler's; one left open, or a word the verifier stops
/// in, a rule it lacks. What is assumed (the scheduler's procedures at
/// their forms' types) is said, not refused. The words of `KNOWN_GAPS`, and
/// only those, do not verify yet.
#[test]
fn every_test_programs_words_verified() {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    let mut t = Tally::default();
    for (name, text) in programs() {
        verify_program(&mut s, &name, &text, &mut t);
    }
    t.unverified.sort();
    assert_eq!(t.unverified, KNOWN_GAPS, "the words not verified are not the known gaps");
    let gap = |x: &String| KNOWN_GAPS.iter().any(|g| x.starts_with(g));
    t.failed.retain(|f| !gap(f));
    t.open_examples.retain(|f| !gap(f));
    t.open -= t.open_gaps;
    t.stopped.retain(|why, _| !t.stopped_gaps.contains(why));
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
    assert!(t.verified + KNOWN_GAPS.len() == t.words && t.words > 5000, "{} of {} words verified", t.verified, t.words);
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
