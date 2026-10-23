//! A program's words verified against their certificates (`typed_cells`),
//! as `fixpt verify` and the REPL's `,verify` do, and the tests: the
//! program checked by the Rust checker, its types kept, compiled by the
//! Rust compiler with certificates, then each word verified.

use crate::cellular::Compiler;
use crate::typed_cells::{verify, Certs, Outcome};
use crate::{Checker, Top};
use fixpt_heap::layout::cellular::WORD_NAME;
use fixpt_heap::{Heap, ObjType, Value};
use fixpt_read::FileId;
use std::time::{Duration, Instant};

/// The Rust checker's forms for `text`, its types kept, `text` loading
/// files from `base`; or why not.
pub fn checked_in(text: &str, base: Option<std::path::PathBuf>) -> Result<(Checker, Vec<Top>), String> {
    let mut c = Checker::new();
    c.base_dir = base;
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

/// `tops`' words, compiled into `heap` with their certificates, settled
/// (`Certs::settle`); or why the program was not compiled. A certificate
/// that does not settle is said in the second.
pub fn certified(heap: &mut Heap, c: &mut Checker, text: &str, tops: &[Top]) -> Result<(Certs, Option<String>), String> {
    let mut certs = {
        let mut comp = Compiler::new(heap, c, text);
        comp.certs = Some(Certs::default());
        comp.program(tops)?;
        comp.certs.take().expect("made")
    };
    let unsettled = certs.settle(c).err();
    Ok((certs, unsettled))
}

/// A word's name, as its code has it; none for a program's own word.
pub fn word_name(heap: &Heap, word: Value) -> Option<String> {
    let named = heap.bloblet_slot(word, WORD_NAME);
    heap.is_a(named, ObjType::Symbol).then(|| heap.symbol_name(named).to_string())
}

/// What verifying a program found: each word, by name, and its outcome;
/// a certificate that did not settle; and how long compiling and
/// verifying took.
pub struct Verified {
    pub words: Vec<(Option<String>, Outcome)>,
    pub unsettled: Option<String>,
    pub compile_time: Duration,
    pub verify_time: Duration,
}

/// `tops`, checked by `c` from `text`, compiled and each word verified, the
/// words kept alive in `scheme`'s scope as they are; or why it was not
/// compiled. Loads are from `base`.
pub fn verify_program(scheme: &mut fixpt_scheme::Session, c: &mut Checker, text: &str, tops: &[Top], base: Option<std::path::PathBuf>) -> Result<Verified, String> {
    crate::syn::set_load_base(base);
    let mut out = Err(String::new());
    scheme.scope(|sc| {
        sc.make(|m| {
            let start = Instant::now();
            let made = certified(m.heap(), c, text, tops);
            let compile_time = start.elapsed();
            out = made.map(|(certs, unsettled)| {
                let start = Instant::now();
                let heap: &Heap = m.heap();
                let words = certs.words.keys().map(|raw| {
                    let w = Value::from_raw(*raw);
                    (word_name(heap, w), verify(c, heap, &certs, w))
                });
                let words = words.collect();
                Verified { words, unsettled, compile_time, verify_time: start.elapsed() }
            });
            Value::NULL
        });
    });
    out
}

/// What verifying `text` found, said in lines: each word that did not
/// verify, and why, or that each did; only the words `only` names, if
/// any; and whether all of those verified. Or why the program was refused,
/// or not compiled.
pub fn report(scheme: &mut fixpt_scheme::Session, text: &str, base: Option<std::path::PathBuf>, only: &[String]) -> Result<(Vec<String>, bool), String> {
    let (mut c, tops) = checked_in(text, base.clone()).map_err(|e| format!("the checker refused it: {e}"))?;
    let v = verify_program(scheme, &mut c, text, &tops, base).map_err(|e| format!("not compiled: {e}"))?;
    let mut lines = Vec::new();
    if let Some(why) = &v.unsettled {
        lines.push(format!("a certificate is not settled: {why}"));
    }
    let shown = |n: &Option<String>| only.is_empty() || n.as_ref().is_some_and(|n| only.contains(n));
    let mut words: Vec<_> = v.words.iter().filter(|(n, _)| shown(n)).collect();
    // By name, the program's own word (`program`) last.
    words.sort_by_key(|(n, _)| (n.as_deref() == Some("program"), n.clone()));
    for want in only.iter().filter(|w| !v.words.iter().any(|(n, _)| n.as_ref() == Some(w))) {
        lines.push(format!("`{want}`: no word of that name"));
    }
    let mut verified = 0;
    for (n, o) in &words {
        let who = n.as_ref().map_or("the top level".to_string(), |n| format!("`{n}`"));
        if o.verified() {
            verified += 1;
            let given = if o.assumed.is_empty() { String::new() } else { format!(", given {} trusted", o.assumed.len()) };
            lines.push(format!("{who}: verified ({} obligations discharged{given})", o.discharged));
            continue;
        }
        lines.push(format!("{who}: not verified"));
        for f in &o.failed {
            lines.push(format!("  fails: {f}"));
        }
        for x in &o.open {
            lines.push(format!("  open, not proved: {x}"));
        }
        if let Some(why) = &o.stopped {
            lines.push(format!("  stopped: {why}"));
        }
    }
    lines.push(format!("{verified} of {} words verified", words.len()));
    if words.iter().any(|(_, o)| !o.open.is_empty()) {
        lines.push("(open: not proved, which is not shown false; `fixpt test` looks for a counterexample)".into());
    }
    let all = verified == words.len() && v.unsettled.is_none() && only.iter().all(|w| v.words.iter().any(|(n, _)| n.as_ref() == Some(w)));
    Ok((lines, all))
}
