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
/// or not compiled. Each VC left open is asked of an SMT solver, if there
/// is one (`crate::smt`), and sorted by what it says (`sorted`).
pub fn report(scheme: &mut fixpt_scheme::Session, text: &str, base: Option<std::path::PathBuf>, only: &[String]) -> Result<(Vec<String>, bool), String> {
    let (mut c, tops) = checked_in(text, base.clone()).map_err(|e| format!("the checker refused it: {e}"))?;
    let v = verify_program(scheme, &mut c, text, &tops, base.clone()).map_err(|e| format!("not compiled: {e}"))?;
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
    let solver = crate::smt::solver();
    let mut replayer = Replayer { text, base, session: None };
    let (mut verified, mut unsorted) = (0, false);
    for (n, o) in &words {
        let who = n.as_ref().map_or("the top level".to_string(), |n| format!("`{n}`"));
        let sorted: Vec<(usize, Sorted)> = match &solver {
            Some(z) => o.vcs.iter().map(|(i, what, vc)| (*i, sort(z, &mut replayer, n.as_deref(), o, what, vc))).collect(),
            None => Vec::new(),
        };
        let proved = |i: usize| sorted.iter().any(|(j, s)| *j == i && matches!(s, Sorted::Proved));
        let by_solver = sorted.iter().filter(|(_, s)| matches!(s, Sorted::Proved)).count();
        let open: Vec<usize> = (0..o.open.len()).filter(|i| !proved(*i)).collect();
        if o.failed.is_empty() && o.stopped.is_none() && open.is_empty() {
            verified += 1;
            let solved = if by_solver == 0 { String::new() } else { format!(", {by_solver} by the SMT solver") };
            let given = if o.assumed.is_empty() { String::new() } else { format!(", given {} trusted", o.assumed.len()) };
            lines.push(format!("{who}: verified ({} obligations discharged{solved}{given})", o.discharged + by_solver));
            continue;
        }
        lines.push(format!("{who}: not verified"));
        for f in &o.failed {
            lines.push(format!("  fails: {f}"));
        }
        for i in open {
            match sorted.iter().find(|(j, _)| *j == i) {
                Some((_, s)) => lines.push(format!("  {}", s.said())),
                None => {
                    unsorted = true;
                    lines.push(format!("  open, not proved: {}", o.open[i]));
                }
            }
        }
        if let Some(why) = &o.stopped {
            lines.push(format!("  stopped: {why}"));
        }
    }
    lines.push(format!("{verified} of {} words verified", words.len()));
    if unsorted {
        let why = if solver.is_none() { "; no SMT solver was found (z3, or `FIXPT_SMT`) to ask" } else { "" };
        lines.push(format!("(open: not proved, which is not shown false{why}; `fixpt test` looks for a counterexample)"));
    }
    let all = verified == words.len() && v.unsettled.is_none() && only.iter().all(|w| v.words.iter().any(|(n, _)| n.as_ref() == Some(w)));
    Ok((lines, all))
}

/// What the solver, and a run of what it found, made of an open VC
/// (`docs/research/specs-and-counterexamples.md`, §3 and §8), each with
/// where it is owed and what is said of it.
enum Sorted {
    Proved,
    /// The solver's counterexample, run, breaks a specification.
    False(String),
    /// The run keeps it: the proof took a callee to return what it does
    /// not.
    NotInductive(String),
    /// Refuted by the solver, but not shown false, nor its callees blamed.
    Refuted(String),
    /// The solver did not decide it.
    Beyond(String),
}

impl Sorted {
    fn said(&self) -> String {
        match self {
            Sorted::Proved => "proved".into(),
            Sorted::False(s) => format!("false: {s}"),
            Sorted::NotInductive(s) => format!("not inductive: {s}"),
            Sorted::Refuted(s) => format!("open: {s}"),
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
    /// how it went, and the input said; none if it cannot be.
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

/// VC `vc` of `word`, owed `what`, which its outcome `o` left open: asked
/// of `solver`; if refuted, its counterexample's parameters run, to tell
/// a false specification from a proof that took a callee to return what
/// it does not.
fn sort(solver: &str, r: &mut Replayer, word: Option<&str>, o: &Outcome, what: &str, vc: &crate::logic::Formula<crate::typed_cells::Term>) -> Sorted {
    use crate::smt::Solved;
    use crate::spec_tests::{written, Tried};
    use crate::typed_cells::{show_term, Term};
    let model = match crate::smt::solve(solver, vc) {
        Solved::Proved => return Sorted::Proved,
        Solved::Unknown(why) => return Sorted::Beyond(format!("{what}: the SMT solver says {why}")),
        Solved::Refuted(m) => m,
    };
    let shown_model = model.iter().map(|(t, v)| format!("{} = {}", show_term(t), written(v))).collect::<Vec<_>>().join(", ");
    let refuted = || Sorted::Refuted(format!("{what}: the SMT solver refutes it, for {shown_model}"));
    let given: Vec<(usize, String)> = model.iter().filter_map(|(t, v)| if let Term::Slot(i) = t { Some((*i, written(v))) } else { None }).collect();
    let Some(word) = word else { return refuted() };
    match r.replay(word, &given) {
        Some((Tried::Broken(c), _, _)) => Sorted::False(format!("{what}: {c}")),
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
                match r.evaluated(&call) {
                    Some(v) if v != written(assumed) => took.push(format!("{call} to be {}; it is {v}", written(assumed))),
                    Some(_) => {}
                    None => took.push(format!("{call} to be {}", written(assumed))),
                }
            }
            if took.is_empty() {
                Sorted::Refuted(format!("{what}: the SMT solver refutes it, for {shown_model}, but run, it holds for {shown}: the proof does not know what the run does"))
            } else {
                Sorted::NotInductive(format!(
                    "{what}: it holds for {shown}, but the proof took {}: what that returns needs saying, in an `ensures`",
                    took.join(", and ")
                ))
            }
        }
        Some((Tried::PassedOver, _, _)) => Sorted::Refuted(format!("{what}: the SMT solver refutes it, for {shown_model}, an input its requires does not take")),
        Some((Tried::Unfinished, shown, _)) => Sorted::Refuted(format!("{what}: the SMT solver refutes it, for {shown_model}; run on {shown}, it did not end in time")),
        Some((Tried::Failed(f), _, _)) => Sorted::Refuted(format!("{what}: the SMT solver refutes it, for {shown_model}; run, it {f}")),
        None => refuted(),
    }
}
