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

/// A word's expressions' cells, from where to where, and their spans.
pub type Sources = Vec<(usize, usize, fixpt_read::Span)>;

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

/// What verifying a program found: each word, by name, its outcome, and
/// its cells' places in the source (`Cert::sources`); a certificate that
/// did not settle; and how long compiling and verifying took.
pub struct Verified {
    pub words: Vec<(Option<String>, Outcome, Sources)>,
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
                    (word_name(heap, w), verify(c, heap, &certs, w), certs.words[raw].sources.clone())
                });
                let words = words.collect();
                Verified { words, unsettled, compile_time, verify_time: start.elapsed() }
            });
            Value::NULL
        });
    });
    out
}

/// Where cell `cell` is in the source: the innermost expression's span
/// whose cells it is among, said as `FILE:LINE:COLUMN` (`file` the
/// program's name; none, and only the source is said) and the
/// expression, shortened. Of a loaded module's text, only that it is.
fn place(text: &str, file: Option<&str>, sources: &Sources, cell: Option<usize>) -> Option<String> {
    let cell = cell?;
    let (_, _, span) = sources.iter().filter(|(a, b, _)| *a <= cell && cell < *b).min_by_key(|(a, b, sp)| (b - a, sp.end - sp.start))?;
    if span.file.0 != 0 {
        return Some("in a loaded module".into());
    }
    let (start, end) = (span.start as usize, (span.end as usize).min(text.len()));
    let source: String = text.get(start..end)?.split_whitespace().collect::<Vec<_>>().join(" ");
    let source = if source.chars().count() > 48 { format!("{}…", source.chars().take(47).collect::<String>()) } else { source };
    let before = &text[..start];
    let line = before.matches('\n').count() + 1;
    let column = before.rsplit('\n').next().map_or(0, |l| l.chars().count()) + 1;
    Some(match file {
        Some(f) => format!("{f}:{line}:{column}, `{source}`"),
        None => format!("`{source}`"),
    })
}

/// What the verifier said of a cell, without the cell (`cell N (r): `),
/// which `place` says instead.
fn bare(said: &str) -> &str {
    match said.strip_prefix("cell ") {
        Some(rest) => rest.split_once("): ").map_or(said, |(_, w)| w),
        None => said,
    }
}

/// What verifying `text` (the program `file` names, if any) found, said
/// in lines: each word that did not verify, and why, each at its place in
/// the source, or that each did; only the words `only` names, if any; and
/// whether all of those verified. Or why the program was refused, or not
/// compiled. Each VC left open is asked of an SMT solver, if there is one
/// (`crate::smt`), and sorted by what it says (`sort`).
pub fn report(scheme: &mut fixpt_scheme::Session, text: &str, file: Option<&str>, base: Option<std::path::PathBuf>, only: &[String]) -> Result<(Vec<String>, bool), String> {
    let (mut c, tops) = checked_in(text, base.clone()).map_err(|e| format!("the checker refused it: {e}"))?;
    let v = verify_program(scheme, &mut c, text, &tops, base.clone()).map_err(|e| format!("not compiled: {e}"))?;
    let mut lines = Vec::new();
    if let Some(why) = &v.unsettled {
        lines.push(format!("a certificate is not settled: {why}"));
    }
    let shown = |n: &Option<String>| only.is_empty() || n.as_ref().is_some_and(|n| only.contains(n));
    let mut words: Vec<_> = v.words.iter().filter(|(n, _, _)| shown(n)).collect();
    // By name, the program's own word (`program`) last.
    words.sort_by_key(|(n, _, _)| (n.as_deref() == Some("program"), n.clone()));
    for want in only.iter().filter(|w| !v.words.iter().any(|(n, _, _)| n.as_ref() == Some(w))) {
        lines.push(format!("`{want}`: no word of that name"));
    }
    let solver = crate::smt::solver();
    let theory = crate::smt_theory::Theory::of(&c, &tops);
    let mut replayer = Replayer { text, base, session: None };
    let (mut verified, mut unsorted) = (0, false);
    for (n, o, sources) in &words {
        let who = n.as_ref().map_or("the top level".to_string(), |n| format!("`{n}`"));
        let at = |cell: Option<usize>, said: &str| match place(text, file, sources, cell) {
            Some(p) => format!("  at {p}: {}", bare(said)),
            None => format!("  {said}"),
        };
        let sorted: Vec<(usize, Sorted)> = match &solver {
            Some(z) => {
                let cx = crate::smt::Context { theory: Some(&theory), lists: !o.writes, conses: &o.conses, finite: &o.finite };
                o.vcs.iter().map(|(i, what, vc)| (*i, sort(z, cx, &mut replayer, n.as_deref(), o, what, vc))).collect()
            }
            None => Vec::new(),
        };
        let proved = |i: usize| sorted.iter().any(|(j, s)| *j == i && matches!(s, Sorted::Proved));
        let by_solver = sorted.iter().filter(|(_, s)| matches!(s, Sorted::Proved)).count();
        let open: Vec<usize> = (0..o.open.len()).filter(|i| !proved(*i)).collect();
        if o.failed.is_empty() && o.stopped.is_none() && open.is_empty() {
            verified += 1;
            let solved = if by_solver == 0 { String::new() } else { format!(", {by_solver} of them by the SMT solver") };
            let given = if o.assumed.is_empty() { String::new() } else { format!(", given {} trusted", o.assumed.len()) };
            lines.push(format!("{who}: verified ({} obligations proved{solved}{given})", o.discharged + by_solver));
            continue;
        }
        lines.push(format!("{who}: not verified"));
        for (k, f) in o.failed.iter().enumerate() {
            lines.push(at(o.failed_at.get(k).copied().flatten(), &format!("fails: {}", bare(f))));
        }
        for i in open {
            let cell = o.open_at.get(i).copied().flatten();
            let what = o.vcs.iter().find(|(j, _, _)| *j == i).map_or(o.open[i].as_str(), |(_, w, _)| w.as_str());
            let said = match sorted.iter().find(|(j, _)| *j == i) {
                Some((_, s)) => format!("{}: {}", bare(what), s.said()),
                None => {
                    unsorted = true;
                    format!("not proved: {}", bare(&o.open[i]))
                }
            };
            lines.push(at(cell, &said));
        }
        if let Some(why) = &o.stopped {
            lines.push(format!("  stopped: {why}"));
        }
    }
    lines.push(format!("{verified} of {} words verified", words.len()));
    if unsorted {
        let why = if solver.is_none() { "; no SMT solver was found (z3, or `FIXPT_SMT`) to ask" } else { "" };
        lines.push(format!("(not proved is not shown false{why}; `fixpt test` looks for a counterexample)"));
    }
    let all = verified == words.len() && v.unsettled.is_none() && only.iter().all(|w| v.words.iter().any(|(n, _, _)| n.as_ref() == Some(w)));
    Ok((lines, all))
}

/// What the solver, and a run of what it found, made of an open VC
/// (`docs/research/specs-and-counterexamples.md`, §3 and §8), with what
/// is said of it.
enum Sorted {
    Proved,
    /// The solver's counterexample, run, breaks a specification.
    False(String),
    /// The run keeps it: the proof took a call to give what it does not.
    NotInductive(String),
    /// Refuted by the solver, but not shown false, nor a call blamed.
    Refuted(String),
    /// The solver did not decide it.
    Beyond(String),
}

impl Sorted {
    fn said(&self) -> String {
        match self {
            Sorted::Proved => "proved".into(),
            Sorted::False(s) => format!("false: {s}"),
            Sorted::NotInductive(s) => format!("not proved, as the proof knows too little of a call. {s}"),
            Sorted::Refuted(s) => format!("not proved. {s}"),
            Sorted::Beyond(s) => format!("beyond the prover: {s}"),
        }
    }
}

/// The program run for replays, its specifications checked, in a session
/// of its own, made when first needed: what it says is the run's, not the
/// session verifying it.
struct Replayer<'a> {
    text: &'a str,
    base: Option<std::path::PathBuf>,
    session: Option<Result<(crate::session::Fx26Session, Vec<(String, Vec<String>)>), String>>,
}

impl Replayer<'_> {
    /// `name` called on `given` (values of its parameters, by position):
    /// how it went, the input said, and its values; none if it cannot be.
    fn replay(&mut self, name: &str, given: &[(usize, String)]) -> Option<(crate::spec_tests::Tried, String, Vec<String>)> {
        let (text, base) = (self.text, self.base.clone());
        let made = self.session.get_or_insert_with(|| {
            let mut s = crate::session::Fx26Session::with_backend(fixpt_engine::Backend::Bytecode).map_err(|e| e.message)?;
            s.checker.base_dir = base;
            let defined = crate::spec_tests::replaying(&mut s, text)?;
            Ok((s, defined))
        });
        let (s, defined) = made.as_mut().ok()?;
        crate::spec_tests::replay(s, defined, name, given).ok().flatten()
    }

    /// Expression `e`'s value in the program's run, if it gives one.
    fn evaluated(&mut self, e: &str) -> Option<String> {
        let (s, _) = self.session.as_mut()?.as_mut().ok()?;
        crate::spec_tests::evaluated(s, e)
    }
}

/// VC `vc` of `word`, which its outcome `o` left open: asked of `solver`;
/// if refuted, its counterexample's parameters run, to tell a false
/// specification from a proof that took a call to give what it does not.
fn sort(solver: &str, cx: crate::smt::Context, r: &mut Replayer, word: Option<&str>, o: &Outcome, _what: &str, vc: &crate::logic::Formula<crate::typed_cells::Term>) -> Sorted {
    use crate::smt::Solved;
    use crate::spec_tests::{written, Tried};
    use crate::typed_cells::{show_term, Term};
    let model = match crate::smt::solve(solver, vc, cx) {
        Solved::Proved => return Sorted::Proved,
        Solved::Unknown(why) => return Sorted::Beyond(format!("the SMT solver says {why}")),
        Solved::Refuted(m) => m,
    };
    let shown_model = model.iter().map(|(t, v)| format!("{} = {}", show_term(t), written(v))).collect::<Vec<_>>().join(", ");
    let refuted = || Sorted::Refuted(format!("The SMT solver finds it does not follow when {shown_model}."));
    let given: Vec<(usize, String)> = model.iter().filter_map(|(t, v)| if let Term::Slot(i) = t { Some((*i, written(v))) } else { None }).collect();
    let Some(word) = word else { return refuted() };
    match r.replay(word, &given) {
        // Its own `ensures` broken, the result said; anything else, whose.
        Some((Tried::Broken(b), _, _)) => Sorted::False(match &b.result {
            Some(r) if b.what == "its ensures" => format!("with {}, the result is {r}", b.input),
            _ => format!("with {}, {} does not hold", b.input, b.what),
        }),
        Some((Tried::Kept(_), shown, args)) => {
            // Each value the proof took a global's call to give, beside
            // what the call, run on the input, gives: the call written out
            // of the input's values, and of the calls before it.
            fn source(t: &Term, args: &[String], calls: &[(Term, String, Vec<Term>)]) -> Option<String> {
                match t {
                    Term::Lit(k) if k.is_fixnum() => Some(k.as_fixnum().to_string()),
                    Term::Lit(k) if *k == fixpt_heap::Value::TRUE => Some("#t".into()),
                    Term::Lit(k) if k.is_false() => Some("#f".into()),
                    Term::Slot(i) => args.get(*i).cloned(),
                    Term::App(f @ ("car" | "cdr"), xs) if xs.len() == 1 => Some(format!("({f} {})", source(&xs[0], args, calls)?)),
                    Term::Made(_) => {
                        let (_, f, xs) = calls.iter().find(|(m, _, _)| m == t)?;
                        let xs = xs.iter().map(|x| source(x, args, calls)).collect::<Option<Vec<_>>>()?;
                        Some(format!("({f}{})", xs.iter().map(|x| format!(" {x}")).collect::<String>()))
                    }
                    _ => None,
                }
            }
            let mut took = Vec::new();
            for (made, _, _) in &o.calls {
                let Some((_, assumed)) = model.iter().find(|(m, _)| m == made) else { continue };
                let Some(call) = source(made, &args, &o.calls) else { continue };
                // As a run prints it, to be compared.
                let printed = assumed.printed();
                match r.evaluated(&call) {
                    Some(v) if v != printed => took.push(format!("{call} could be {printed}, where it is {v}")),
                    Some(_) => {}
                    None => took.push(format!("{call} could be {printed}")),
                }
            }
            if took.is_empty() {
                Sorted::Refuted(format!("The SMT solver finds it does not follow when {shown_model}, but run, it holds for {shown}: the proof lacks a fact the run has."))
            } else {
                Sorted::NotInductive(format!(
                    "It holds for {shown}; but for all the proof knows, {}. An `ensures` saying what that returns may let it be proved.",
                    took.join(", and ")
                ))
            }
        }
        Some((Tried::PassedOver, _, _)) => Sorted::Refuted(format!("The SMT solver finds it does not follow when {shown_model}, an input the requires does not take.")),
        Some((Tried::Unfinished, shown, _)) => Sorted::Refuted(format!("The SMT solver finds it does not follow when {shown_model}; run on {shown}, it did not end in time.")),
        Some((Tried::Failed(f), _, _)) => Sorted::Refuted(format!("The SMT solver finds it does not follow when {shown_model}; run, it {f}.")),
        None => refuted(),
    }
}
