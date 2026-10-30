//! Specifications tested by running them (`docs/research/specs-and-counterexamples.md`,
//! S1): a program's procedures called on inputs drawn from their parameters'
//! types, every specification checked as it runs, so that a false one is
//! shown false by an input, with no prover.
//!
//! The program is run with each specified `lambda`'s body checking its own
//! specification (`instrumented`): its `requires` where it starts, its
//! `ensures` of what it gives; one that does not hold fails, naming whose
//! it is. Then each procedure that does nothing another run could see (no
//! write, I/O or transfer of control in its effect) and takes only
//! parameters whose values are drawn here (`int`, `nat`, `bool`, lists of
//! those) is called on drawn inputs:
//!
//! - an input its own `requires` does not hold of, or that an `assume` it
//!   makes does not take, is passed over;
//! - a run in which a specification does not hold (its own `ensures`, or a
//!   callee's `requires` or `ensures`), or an `assert` does not, is a
//!   counterexample;
//! - a run that fails otherwise (`car` of `nil`) is said, as a failure.
//!
//! A *harness* is then just a procedure, of `unit` result say, that
//! `assert`s what it tests; its parameters are what the note's `any`
//! would have given it. Inputs are drawn the same way each time: small and
//! edge values first, then pseudo-random ones from a fixed seed. A run that
//! does not end within the session's step limit says nothing (correctness
//! here is partial).

use crate::ast::{Atom, Named, Spec, Ty, TyId};
use crate::logic::{Expr, Formula};
use crate::session::Fx26Session;
use fixpt_read::{Datum, FileId};

/// What testing one procedure found.
#[derive(Debug)]
pub struct Tested {
    /// The procedure's name; or, of an expression of the program's own,
    /// the expression (`expression`).
    pub name: String,
    pub expression: bool,
    /// The inputs run, those passed over (a `requires` or `assume` that
    /// did not hold of them), and those that did not end in time.
    pub runs: usize,
    pub passed_over: usize,
    pub unfinished: usize,
    /// The first input it was shown false of, and how.
    pub counterexample: Option<String>,
    /// The first run that failed otherwise (`car` of `nil`, say), of an
    /// input it took.
    pub failure: Option<String>,
}

/// A parameter's values, as they are written: an integer, a natural, a
/// natural of a known size (its one value), a `bool`, a list of one of
/// those at a type to give the list.
#[derive(Clone)]
enum Draw {
    Int,
    Nat,
    Exactly(i64),
    Bool,
    List(Box<Draw>, String),
}

/// The edge values an integer is drawn from first.
const EDGES: [i64; 13] = [0, 1, -1, 2, -2, 3, -3, 5, -5, 10, -10, 100, -100];

/// Run program `text` in `session`, its specifications checked as it runs
/// (`instrumented`), then test each of its procedures that can be, `runs`
/// inputs each. An error if the program does not check, or fails.
pub fn test_program(session: &mut Fx26Session, text: &str, runs: usize) -> Result<Vec<Tested>, String> {
    let (checked, defined) = instrumented(session, text)?;
    // Its definitions, then each expression of its own, apart: one in which
    // a specification does not hold is a counterexample, the program's.
    let forms = session.checker.read_in(FileId(0), &checked).map_err(|e| e.message)?;
    let piece = |f: &fixpt_read::Syntax| &checked[f.span.start as usize..f.span.end as usize];
    let defines = |f: &fixpt_read::Syntax| match &f.datum {
        Datum::List { items, .. } => items.first().and_then(|h| h.as_symbol()).is_some_and(|h| session.checker.interner.name(h).starts_with("define")),
        _ => false,
    };
    let (defs, exps): (Vec<&fixpt_read::Syntax>, Vec<&fixpt_read::Syntax>) = forms.iter().partition(|f| defines(f));
    let defs: String = defs.iter().map(|f| format!("{}\n", piece(f))).collect();
    let exps: Vec<String> = exps.iter().map(|f| piece(f).to_string()).collect();
    if let Err(e) = session.run_program(&defs).map_err(|e| e.message)? {
        return Err(format!("the program's definitions fail: {e}"));
    }
    let mut out = Vec::new();
    for e in exps {
        let mut t = Tested { name: e.clone(), expression: true, runs: 1, passed_over: 0, unfinished: 0, counterexample: None, failure: None };
        match run(session, &e)? {
            Ran::Asserted => t.counterexample = Some("an `assert` does not hold".into()),
            Ran::Failed(m) if m.contains("does not hold") => t.counterexample = Some(m.rsplit_once(": ").map_or(m.as_str(), |(_, w)| w).to_string()),
            Ran::Failed(m) => t.failure = Some(format!("fails: {m}")),
            Ran::PassedOver => t.passed_over = 1,
            Ran::Unfinished => t.unfinished = 1,
            Ran::Value(_) => continue,
        }
        out.push(t);
    }
    for (name, params) in defined {
        let Some(n) = session.checker.interner.get(&name) else { continue };
        let Some(t) = session.checker.global_type(n) else { continue };
        if let Some((draws, spec)) = testable(session, t) {
            out.push(test_one(session, &name, &params, &draws, spec.as_ref(), runs)?);
        }
    }
    Ok(out)
}

/// The prefix of a specified procedure's copy that does not check its
/// specification: what a counterexample's result is shown by.
const PLAIN: &str = "%plain-";

/// Program `text` with each specified `lambda` defined at top level
/// checking its specification as it runs: its body `(begin (if REQUIRES
/// #u (error …)) (let ((%r (begin BODY …))) (begin (if ENSURES #u (error
/// …)) %r)))`; and, after it, a copy of the definition as written, named
/// `%plain-NAME`. With the names the program defines, in order, each with
/// its `lambda`'s parameters' names, if it is one.
fn instrumented(session: &Fx26Session, text: &str) -> Result<(String, Vec<(String, Vec<String>)>), String> {
    let mut c = session.fresh_checker();
    let forms = c.read_in(FileId(0), text).map_err(|e| e.message)?;
    let done = c.declare_ahead(&forms).map_err(|e| e.message)?;
    for (f, done) in forms.iter().zip(done) {
        if !done {
            c.top_all(f).map_err(|e| e.message)?;
        }
    }
    let mut names: Vec<(String, Vec<String>)> = Vec::new();
    // Each body replaced, by where it is; each copy, after its form.
    let mut edits: Vec<(usize, usize, String)> = Vec::new();
    for f in &forms {
        let Datum::List { items, .. } = &f.datum else { continue };
        let Some(head) = items.first().and_then(|h| h.as_symbol()) else { continue };
        let head = c.interner.name(head).to_string();
        let (Some(n), true) = (items.get(1).and_then(|n| n.as_symbol()), matches!(head.as_str(), "define" | "define*")) else { continue };
        let name = c.interner.name(n).to_string();
        let k = match names.iter().position(|(m, _)| *m == name) {
            Some(k) => k,
            None => {
                names.push((name.clone(), Vec::new()));
                names.len() - 1
            }
        };
        let Some(lambda) = items.last() else { continue };
        let Datum::List { items: parts, .. } = &lambda.datum else { continue };
        let ([lam, params, body @ ..], false) = (&parts[..], parts.len() < 3) else { continue };
        if lam.as_symbol().map(|l| c.interner.name(l)) != Some("lambda") {
            continue;
        }
        let ps: Vec<String> = match &params.datum {
            Datum::Nil => Vec::new(),
            Datum::List { items, tail: None } => items
                .iter()
                .map(|p| match &p.datum {
                    Datum::Symbol(x) => Some(c.interner.name(*x).to_string()),
                    Datum::List { items, .. } => items.first().and_then(|x| x.as_symbol()).map(|x| c.interner.name(x).to_string()),
                    _ => None,
                })
                .collect::<Option<Vec<_>>>()
                .unwrap_or_default(),
            _ => continue,
        };
        names[k].1 = ps.clone();
        let Some(spec) = c.global_type(n).and_then(|t| c.spec_of(t)) else { continue };
        if ps.len() != spec.params.len() {
            continue;
        }
        let (first, last) = (body[0].span.start as usize, body[body.len() - 1].span.end as usize);
        let checks = |which: &str, f: &Formula<Named>| format!("(if {} #u (error \"the {which} of {name} does not hold\"))", source(&c, f, &ps));
        // The body's value at the result's type, as the type had it there.
        let result = match c.arena.get(c.arena.resolve(c.global_type(n).expect("typed"))) {
            crate::ast::Ty::Subr { result, .. } => c.show_ty(*result),
            _ => continue,
        };
        let wrapped = format!(
            "(begin {} (let ((%r (the {result} (begin {})))) (begin {} %r)))",
            checks("requires", &spec.requires),
            &text[first..last],
            checks("ensures", &spec.ensures)
        );
        edits.push((first, last, wrapped));
        // The logic functions the specification calls, bound around the
        // `lambda`, so that checking it reads no global the procedure's
        // effect does not say; the procedure itself a local `letrec`'s
        // inside, so that it still calls itself (a `define` of no `lambda`
        // binds its name only once made).
        let mut called = Vec::new();
        calls_in(&spec.requires, &mut called);
        calls_in(&spec.ensures, &mut called);
        if let (false, [_, _, ty, _]) = (called.is_empty(), &items[..]) {
            let bound: String = called.iter().map(|g| format!("({0} {0})", c.interner.name(*g))).collect::<Vec<_>>().join(" ");
            let ty = &text[ty.span.start as usize..ty.span.end as usize];
            edits.push((lambda.span.start as usize, lambda.span.start as usize, format!("(let ({bound}) (letrec (({name} {ty} ")));
            edits.push((lambda.span.end as usize, lambda.span.end as usize, format!(")) {name}))")));
        }
        let end = f.span.end as usize;
        let plain = format!("\n({head} {PLAIN}{name}{}", &text[items[1].span.end as usize..end]);
        edits.push((end, end, plain));
    }
    edits.sort_by_key(|(a, b, _)| std::cmp::Reverse((*a, *b)));
    let mut out = text.to_string();
    for (a, b, r) in edits {
        out.replace_range(a..b, &r);
    }
    Ok((out, names))
}

/// The logic functions `f` calls (`Named::Call`), each once, onto `out`.
fn calls_in(f: &Formula<Named>, out: &mut Vec<fixpt_read::Sym>) {
    fn named(n: &Named, out: &mut Vec<fixpt_read::Sym>) {
        if let Named::Call(g, xs) = n {
            if !out.contains(g) {
                out.push(*g);
            }
            for x in xs.iter() {
                atoms(x, out);
            }
        }
    }
    fn atoms(e: &Expr<Named>, out: &mut Vec<fixpt_read::Sym>) {
        match e {
            Expr::Atom(n) => named(n, out),
            Expr::Lit(_) => {}
            Expr::Add(x, y) | Expr::Sub(x, y) | Expr::Mul(x, y) => {
                atoms(x, out);
                atoms(y, out);
            }
        }
    }
    match f {
        Formula::True | Formula::False => {}
        Formula::Rel(_, x, y) => {
            atoms(x, out);
            atoms(y, out);
        }
        Formula::Holds(n) => named(n, out),
        Formula::Not(p) => calls_in(p, out),
        Formula::And(ps) | Formula::Or(ps) => ps.iter().for_each(|p| calls_in(p, out)),
        Formula::Implies(p, q) => {
            calls_in(p, out);
            calls_in(q, out);
        }
    }
}

/// What `t`, a global's type, is tested as, if it is a specified
/// procedure's or a harness's: its parameters' draws, and its
/// specification.
fn testable(session: &Fx26Session, t: TyId) -> Option<(Vec<Draw>, Option<Spec>)> {
    // Every procedure is tested that can be: what it calls checks its
    // specifications as it runs.
    let c = &session.checker;
    let Ty::Subr { effect, params, result, spec, .. } = c.arena.get(c.arena.resolve(t)).clone() else { return None };
    let seen = |a: &Atom| matches!(a, Atom::Write(_) | Atom::Init(_) | Atom::Send(_) | Atom::Receive(_) | Atom::Await(_) | Atom::Io(_) | Atom::Goto(_) | Atom::Comefrom(_) | Atom::Nondet | Atom::Stage | Atom::Var(_) | Atom::App(_));
    if effect.0.iter().any(seen) {
        return None;
    }
    let draws = params.iter().map(|p| draw_of(session, *p)).collect::<Option<Vec<_>>>()?;
    let _ = result;
    let spec = spec.map(|s| (*s).clone()).filter(|s| !s.requires.trivial() || !s.ensures.trivial());
    Some((draws, spec))
}

fn draw_of(session: &Fx26Session, t: TyId) -> Option<Draw> {
    let c = &session.checker;
    let t = c.arena.resolve(t);
    match c.arena.get(t).clone() {
        _ if t == c.int => Some(Draw::Int),
        _ if t == c.bool_ => Some(Draw::Bool),
        Ty::Nat(crate::ast::Size::Finite) => Some(Draw::Nat),
        Ty::Nat(n) => n.as_lit().map(Draw::Exactly),
        Ty::Pair(e, tail, _, true) if c.arena.resolve(tail) == t => Some(Draw::List(Box::new(draw_of(session, e)?), c.show_ty(t))),
        _ => None,
    }
}

/// A fixed sequence of pseudo-random numbers (a linear congruential
/// generator, Knuth's constants).
struct Seq(u64);

impl Seq {
    fn next(&mut self, below: u64) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        (self.0 >> 33) % below
    }
}

/// The `k`th value of draw `d`, for parameter `j`, as written.
fn value(d: &Draw, k: usize, j: usize, seq: &mut Seq) -> String {
    let int = |seq: &mut Seq| if k < EDGES.len() { EDGES[(k + 3 * j) % EDGES.len()] } else { seq.next(201) as i64 - 100 };
    match d {
        Draw::Int => int(seq).to_string(),
        Draw::Nat => int(seq).abs().to_string(),
        Draw::Exactly(k) => k.to_string(),
        Draw::Bool => if (k + j) % 2 == 0 { "#t" } else { "#f" }.to_string(),
        Draw::List(e, t) => {
            let n = if k < 5 { k } else { seq.next(6) as usize };
            let xs: Vec<String> = (0..n).map(|i| value(e, k + i + 1, j + i, seq)).collect();
            if xs.is_empty() { format!("(the {t} nil)") } else { format!("(the {t} (list {}))", xs.join(" ")) }
        }
    }
}

/// A proposition of a specification as an expression of FX-26, each
/// parameter by `names`, the result `%r`.
fn source(c: &crate::Checker, f: &Formula<Named>, names: &[String]) -> String {
    fn atom(c: &crate::Checker, n: &Named, names: &[String]) -> String {
        let p = |i: usize| names.get(i).cloned().unwrap_or_else(|| "?".into());
        match *n {
            Named::Param(i) => p(i),
            Named::Result => "%r".into(),
            Named::Length(i) => format!("(length {})", p(i)),
            Named::Shape(i, k) => format!("({} {})", crate::check::SHAPES[k].1, p(i)),
            Named::Acyclic(i) => format!("(acyclic? {})", p(i)),
            Named::Nat(i) => format!("(nat? {})", p(i)),
            Named::LengthIs(i, j) => format!("(length-is? {} {})", p(i), p(j)),
            // A logic function's call, as written: the global called.
            Named::Call(g, ref xs) => {
                let xs: String = xs.iter().map(|x| format!(" {}", crate::logic::show_expr(x, &|n: &Named| atom(c, n, names)))).collect();
                format!("({}{xs})", c.name(g))
            }
        }
    }
    let atom = |n: &Named| atom(c, n, names);
    let expr = |e: &Expr<Named>| crate::logic::show_expr(e, &atom);
    let all = |ps: &[Formula<Named>]| ps.iter().map(|p| format!(" {}", source(c, p, names))).collect::<String>();
    match f {
        Formula::True => "#t".into(),
        Formula::False => "#f".into(),
        Formula::Rel(r, x, y) => {
            let (x, y) = (expr(x), expr(y));
            match r {
                crate::ast::Rel::Lt => format!("(< {x} {y})"),
                crate::ast::Rel::Le => format!("(<= {x} {y})"),
                crate::ast::Rel::Eq => format!("(= {x} {y})"),
                crate::ast::Rel::Ne => format!("(not (= {x} {y}))"),
            }
        }
        Formula::Holds(n) => atom(n),
        Formula::Not(p) => format!("(not {})", source(c, p, names)),
        Formula::And(ps) if ps.is_empty() => "#t".into(),
        Formula::And(ps) => format!("(and{})", all(ps)),
        Formula::Or(ps) if ps.is_empty() => "#f".into(),
        Formula::Or(ps) => format!("(or{})", all(ps)),
        Formula::Implies(p, q) => format!("(or (not {}) {})", source(c, p, names), source(c, q, names)),
    }
}

/// How a run ended: with a value, written; passed over (an `assume` that
/// did not hold); out of steps; an `assert` that did not hold; failing
/// otherwise.
enum Ran {
    Value(String),
    PassedOver,
    Unfinished,
    Asserted,
    Failed(String),
}

fn run(session: &mut Fx26Session, text: &str) -> Result<Ran, String> {
    Ok(match session.run_program(text).map_err(|e| format!("{text}: {}", e.message))? {
        Ok(v) => Ran::Value(v),
        Err(e) if e.contains("assumption not met") => Ran::PassedOver,
        Err(e) if e.contains("assertion failed") => Ran::Asserted,
        Err(e) if e.contains("step") && e.contains("limit") => Ran::Unfinished,
        Err(e) => Ran::Failed(e),
    })
}

/// How a call on an input went: it kept every specification, giving
/// this; it was passed over; it did not end in time; a specification or
/// an `assert` did not hold (`Broken`); it failed otherwise.
pub enum Tried {
    Kept(String),
    PassedOver,
    Unfinished,
    Broken(Broken),
    Failed(String),
}

/// A specification that did not hold in a run: whose it was (`its
/// ensures`, `the requires of clamp`, `an `assert``), the input said, and,
/// of its own `ensures`, the result.
pub struct Broken {
    pub what: String,
    pub input: String,
    pub result: Option<String>,
}

impl Broken {
    /// As `fixpt test` says it.
    pub fn said(&self) -> String {
        let r = self.result.as_ref().map_or(String::new(), |r| format!(": the result is {r}"));
        format!("{} does not hold, for {}{r}", self.what, self.input)
    }
}

/// `name` called on `args`, in a session running its program
/// `instrumented`.
fn tried(session: &mut Fx26Session, name: &str, args: &[String], shown: &str) -> Result<Tried, String> {
    let call = |f: &str| format!("({f} {})", args.join(" ")).replace(" )", ")");
    Ok(match run(session, &call(name))? {
        Ran::Value(v) => Tried::Kept(v),
        Ran::PassedOver => Tried::PassedOver,
        Ran::Unfinished => Tried::Unfinished,
        Ran::Asserted => Tried::Broken(Broken { what: "an `assert`".into(), input: shown.into(), result: None }),
        // A specification that does not hold: its own `ensures`, shown
        // with the result its copy that does not check gives; or what it
        // calls, said by whose.
        Ran::Failed(e) if e.contains(&format!("the ensures of {name} does not hold")) => {
            let result = match run(session, &call(&format!("{PLAIN}{name}")))? {
                Ran::Value(v) => Some(v),
                _ => None,
            };
            Tried::Broken(Broken { what: "its ensures".into(), input: shown.into(), result })
        }
        Ran::Failed(e) if e.contains("does not hold") => {
            let what = e.rsplit_once("the ").map_or(e.as_str(), |(_, w)| w).trim_end_matches(" does not hold");
            Tried::Broken(Broken { what: format!("the {what}"), input: shown.into(), result: None })
        }
        Ran::Failed(e) => Tried::Failed(format!("fails for {shown}: {e}")),
    })
}

/// A procedure's parameters' names (its specification's, else its
/// `lambda`'s) and draws, by its name in a session running its program
/// `instrumented` (`replaying`); none if it cannot be called on drawn
/// values.
fn callable(session: &Fx26Session, name: &str, params: &[String]) -> Option<(Vec<String>, Vec<Draw>, Option<Spec>)> {
    let n = session.checker.interner.get(name)?;
    let (draws, spec) = testable(session, session.checker.global_type(n)?)?;
    let names = (0..draws.len())
        .map(|i| match spec.as_ref().and_then(|s| s.params.get(i).copied().flatten()) {
            Some(n) => session.checker.interner.name(n).to_string(),
            None => params.get(i).cloned().unwrap_or(format!("%p{i}")),
        })
        .collect();
    Some((names, draws, spec))
}

/// Program `text`, run in `session` with its specifications checked as it
/// runs, its definitions only: for calls to replay (`replay`). The names
/// it defines, each with its `lambda`'s parameters.
pub fn replaying(session: &mut Fx26Session, text: &str) -> Result<Vec<(String, Vec<String>)>, String> {
    let (checked, defined) = instrumented(session, text)?;
    let forms = session.checker.read_in(FileId(0), &checked).map_err(|e| e.message)?;
    let defines = |f: &fixpt_read::Syntax| match &f.datum {
        Datum::List { items, .. } => items.first().and_then(|h| h.as_symbol()).is_some_and(|h| session.checker.interner.name(h).starts_with("define")),
        _ => false,
    };
    let defs: String = forms.iter().filter(|f| defines(f)).map(|f| format!("{}\n", &checked[f.span.start as usize..f.span.end as usize])).collect();
    if let Err(e) = session.run_program(&defs).map_err(|e| e.message)? {
        return Err(format!("the program's definitions fail: {e}"));
    }
    Ok(defined)
}

/// `name`, of a program `replaying` ran, called on the values `given`
/// some of its parameters, by position (as written: `5`, `#t`), the rest
/// their first drawn value: how it went, the input said, and its values
/// as written. None if it cannot be called so.
pub fn replay(session: &mut Fx26Session, defined: &[(String, Vec<String>)], name: &str, given: &[(usize, String)]) -> Result<Option<(Tried, String, Vec<String>)>, String> {
    let params = defined.iter().find(|(n, _)| n == name).map(|(_, ps)| ps.clone()).unwrap_or_default();
    let Some((names, draws, spec)) = callable(session, name, &params) else { return Ok(None) };
    let mut seq = Seq(0x5eed);
    // A value given of the parameter's kind only: a list's a list (`nil`,
    // `(list …)`), at the parameter's type; an integer the logic gives a
    // list (`smt`'s constants) is none of its values.
    let given_for = |j: usize, d: &Draw| {
        let (_, v) = given.iter().find(|(i, _)| *i == j)?;
        let list = v == "nil" || v.starts_with("(list");
        match d {
            Draw::List(_, t) if list => Some(format!("(the {t} {v})")),
            Draw::List(..) => None,
            _ if list => None,
            _ => Some(v.clone()),
        }
    };
    let args: Vec<String> = draws.iter().enumerate().map(|(j, d)| given_for(j, d).unwrap_or_else(|| value(d, 0, j, &mut seq))).collect();
    // Not an input of its own `requires`: passed over.
    let bound = names.iter().zip(&args).map(|(n, a)| format!("({n} {a})")).collect::<Vec<_>>().join(" ");
    if let Some(s) = &spec
        && !s.requires.trivial()
        && matches!(run(session, &format!("(let ({bound}) {})", source(&session.checker, &s.requires, &names)))?, Ran::Value(v) if v == "#f")
    {
        return Ok(Some((Tried::PassedOver, bound, args)));
    }
    let shown = if args.is_empty() { "no input".to_string() } else { names.iter().zip(&args).map(|(n, a)| format!("{n} = {a}")).collect::<Vec<_>>().join(", ") };
    tried(session, name, &args, &shown).map(|t| Some((t, shown, args)))
}

/// Expression `e`'s value, as written, in a session running a program
/// `replaying` ran; none if it does not give one.
pub fn evaluated(session: &mut Fx26Session, e: &str) -> Option<String> {
    match run(session, e) {
        Ok(Ran::Value(v)) => Some(v),
        _ => None,
    }
}

/// A value of the logic's as FX-26 writes it.
pub fn written(v: &crate::smt::Val) -> String {
    match v {
        crate::smt::Val::Int(k) => k.to_string(),
        crate::smt::Val::Bool(b) => if *b { "#t" } else { "#f" }.to_string(),
        crate::smt::Val::List(xs) if xs.is_empty() => "nil".into(),
        crate::smt::Val::List(xs) => format!("(list{})", xs.iter().map(|x| format!(" {}", written(x))).collect::<String>()),
    }
}

fn test_one(session: &mut Fx26Session, name: &str, params: &[String], draws: &[Draw], spec: Option<&Spec>, runs: usize) -> Result<Tested, String> {
    // Each parameter by its specification's name, else its `lambda`'s.
    let names: Vec<String> = (0..draws.len())
        .map(|i| match spec.and_then(|s| s.params.get(i).copied().flatten()) {
            Some(n) => session.checker.interner.name(n).to_string(),
            None => params.get(i).cloned().unwrap_or(format!("%p{i}")),
        })
        .collect();
    let mut t = Tested { name: name.to_string(), expression: false, runs: 0, passed_over: 0, unfinished: 0, counterexample: None, failure: None };
    let mut seq = Seq(0x5eed);
    // Of no parameters, one input.
    for k in 0..if draws.is_empty() { 1 } else { runs } {
        let args: Vec<String> = draws.iter().enumerate().map(|(j, d)| value(d, k, j, &mut seq)).collect();
        let bound = names.iter().zip(&args).map(|(n, a)| format!("({n} {a})")).collect::<Vec<_>>().join(" ");
        let shown = if args.is_empty() { "no input".to_string() } else { names.iter().zip(&args).map(|(n, a)| format!("{n} = {a}")).collect::<Vec<_>>().join(", ") };
        t.runs += 1;
        // Not an input of its own `requires`.
        if let Some(s) = spec
            && !s.requires.trivial()
            && matches!(run(session, &format!("(let ({bound}) {})", source(&session.checker, &s.requires, &names)))?, Ran::Value(v) if v == "#f")
        {
            t.passed_over += 1;
            continue;
        }
        match tried(session, name, &args, &shown)? {
            Tried::Kept(_) => {}
            Tried::PassedOver => t.passed_over += 1,
            Tried::Unfinished => t.unfinished += 1,
            Tried::Broken(b) => {
                t.counterexample = Some(b.said());
                break;
            }
            Tried::Failed(f) => {
                t.failure.get_or_insert(f);
            }
        }
    }
    Ok(t)
}
