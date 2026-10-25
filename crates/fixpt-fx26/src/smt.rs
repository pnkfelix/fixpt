//! The verifier's open VCs given to an SMT solver
//! (`docs/research/specs-and-counterexamples.md`, S2): each written as
//! SMT-LIB, its denial asserted, and the solver asked whether that is
//! satisfiable. Unsatisfiable, the VC is proved; satisfiable, the values
//! the solver gives its terms are a counterexample to it, for
//! `crate::verifying` to replay; neither (a timeout, a product of unknowns
//! it gave up on), it is beyond the solver.
//!
//! Each term is a constant of its own: an integer where an expression has
//! it, a boolean where a proposition does (`Holds`). Two terms the solver
//! does not know equal may then be given different values, which only
//! loses proofs: sound. Integers are the logic's, unbounded, as FX-26's.
//! A logic function's call (`Term::Call`) is its definition's, if the
//! theory has one (`crate::smt_theory`), else an uninterpreted function
//! applied, of a `Bool` or an `Int` by where it stands, its arguments
//! integers (a value not an integer is a constant all the same: the
//! solver compares, and nothing else, as congruence asks).
//!
//! Where the word writes nothing (`Context::lists`), a term the VC uses
//! as a list is one of the theory's lists, of the sort its type gives
//! (`Context::finite`): `(car x)` its head, `(cdr x)` its tail, `(eq x
//! nil)` its being `nil`, and what `cons` made, the pair of its parts.
//! (Where a pair may be written, what was read of it is not what it
//! holds, and these say nothing.)
//!
//! The solver is z3, run as `z3 -in`, or what `FIXPT_SMT` names; none, and
//! nothing is asked.

use crate::logic::{Expr, Formula};
use crate::smt_theory::{Sort, Theory, symbol};
use crate::typed_cells::Term;
use std::io::Write;
use std::process::{Command, Stdio};
use std::rc::Rc;

/// A value the solver gave a term.
#[derive(Clone, Debug, PartialEq)]
pub enum Val {
    Int(i128),
    Bool(bool),
    List(Vec<Val>),
}

impl Val {
    /// As a run prints it: `5`, `#t`, `(1 (2) ())`.
    pub fn printed(&self) -> String {
        match self {
            Val::Int(k) => k.to_string(),
            Val::Bool(b) => if *b { "#t" } else { "#f" }.into(),
            Val::List(xs) => format!("({})", xs.iter().map(Val::printed).collect::<Vec<_>>().join(" ")),
        }
    }
}

/// What the solver said of a VC.
#[derive(Debug)]
pub enum Solved {
    Proved,
    /// Its denial holds of these values: the hypotheses, and not the goal.
    Refuted(Vec<(Term, Val)>),
    /// Neither, and why: the solver's word for it.
    Unknown(String),
}

/// What a VC is asked in: the logic functions defined, and, if the word
/// writes nothing, the pairs it made (`Outcome::conses`), its terms of
/// lists the theory's.
#[derive(Clone, Copy, Default)]
pub struct Context<'a> {
    pub theory: Option<&'a Theory>,
    pub lists: bool,
    pub conses: &'a [(Term, Term, Term)],
    /// The terms of finite lists (`Outcome::finite`), each with its sort:
    /// only these, their tails, the lists their elements are, and `nil`
    /// are the theory's lists, which are all finite.
    pub finite: &'a [(Term, Sort)],
}

impl Context<'_> {
    /// `f`'s parameters' sorts and its result's, if the theory defines it.
    fn signature(&self, f: &str) -> Option<(&[Sort], Sort)> {
        self.theory?.signature(f)
    }
}

/// The solver's command, if there is one: `FIXPT_SMT`, else `z3` where it
/// runs.
pub fn solver() -> Option<String> {
    let cmd = std::env::var("FIXPT_SMT").unwrap_or_else(|_| "z3".into());
    let runs = Command::new(&cmd).arg("-version").stdout(Stdio::null()).stderr(Stdio::null()).status();
    runs.is_ok_and(|s| s.success()).then_some(cmd)
}

/// How long the solver is given for one VC, in milliseconds.
const TIMEOUT_MS: u32 = 2000;

/// `vc` asked of `solver`, in `cx`.
pub fn solve(solver: &str, vc: &Formula<Term>, cx: Context) -> Solved {
    let mut w = Writer { cx, ..Default::default() };
    if cx.lists {
        w.lists_of(vc);
    }
    let denied = format!("(not {})", w.formula(vc));
    // The pairs made, of those the VC has as lists, each its parts.
    let mut made = Vec::new();
    for (m, a, d) in cx.conses {
        if let Some(l) = w.sort_in(m)
            && let Some(h) = w.element(a, l.elem().expect("a list's"))
            && w.fits(d, &l)
        {
            let (m, d) = (w.list_term(m, &l), w.list_term(d, &l));
            made.push(format!("(assert (= {m} (cons {h} {d})))"));
        }
    }
    let mut q = String::from("(set-option :produce-models true)\n(set-logic ALL)\n");
    match cx.theory {
        Some(th) if cx.lists || !th.definitions.is_empty() => q += &th.prelude(),
        None if cx.lists => q += &format!("{}\n", crate::smt_theory::LISTS),
        _ => {}
    }
    for (i, _) in w.ints.iter().enumerate() {
        q += &format!("(declare-const i{i} Int)\n");
    }
    for (i, _) in w.bools.iter().enumerate() {
        q += &format!("(declare-const b{i} Bool)\n");
    }
    for (i, (_, l)) in w.lists.iter().enumerate() {
        q += &format!("(declare-const l{i} {})\n", l.name());
    }
    for (i, (_, n, b)) in w.funs.iter().enumerate() {
        q += &format!("(declare-fun f{i} ({}) {})\n", vec!["Int"; *n].join(" "), if *b { "Bool" } else { "Int" });
    }
    for m in made {
        q += &m;
        q.push('\n');
    }
    q += &format!("(assert {denied})\n(check-sat)\n");
    let names: Vec<String> = (0..w.ints.len()).map(|i| format!("i{i}")).chain((0..w.bools.len()).map(|i| format!("b{i}"))).chain((0..w.lists.len()).map(|i| format!("l{i}"))).collect();
    if !names.is_empty() {
        q += &format!("(get-value ({}))\n", names.join(" "));
    }
    let out = match ask(solver, &q) {
        Ok(o) => o,
        Err(e) => return Solved::Unknown(e),
    };
    let mut lines = out.lines();
    match lines.next().map(str::trim) {
        Some("unsat") => Solved::Proved,
        Some("sat") => {
            let rest: String = lines.collect::<Vec<_>>().join(" ");
            let model = values(&rest).into_iter().filter_map(|(n, v)| {
                let k: usize = n[1..].parse().ok()?;
                let t = match &n[..1] {
                    "i" => w.ints.get(k),
                    "b" => w.bools.get(k),
                    _ => w.lists.get(k).map(|(t, _)| t),
                };
                Some((t?.clone(), v))
            });
            Solved::Refuted(model.collect())
        }
        Some(other) => Solved::Unknown(other.to_string()),
        None => Solved::Unknown("no answer".into()),
    }
}

fn ask(solver: &str, q: &str) -> Result<String, String> {
    let mut child = Command::new(solver)
        .args(["-in", "-smt2", &format!("-t:{TIMEOUT_MS}")])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .map_err(|e| format!("{solver}: {e}"))?;
    child.stdin.take().expect("piped").write_all(q.as_bytes()).map_err(|e| e.to_string())?;
    let out = child.wait_with_output().map_err(|e| e.to_string())?;
    Ok(String::from_utf8_lossy(&out.stdout).into_owned())
}

/// The terms named so far, an integer's, a boolean's and a list's, by
/// number; the uninterpreted functions called; the terms that are lists.
#[derive(Default)]
struct Writer<'a> {
    cx: Context<'a>,
    ints: Vec<Term>,
    bools: Vec<Term>,
    lists: Vec<(Term, Sort)>,
    /// The functions called with no definition: each one's name, how many
    /// arguments, and whether of a `Bool`.
    funs: Vec<(Rc<str>, usize, bool)>,
    list: Vec<(Term, Sort)>,
}

/// Whether `t` is `nil`.
fn is_nil(t: &Term) -> bool {
    matches!(t, Term::Lit(v) if *v == fixpt_heap::Value::NULL)
}

impl Writer<'_> {
    fn named(names: &mut Vec<Term>, t: &Term) -> usize {
        names.iter().position(|n| n == t).unwrap_or_else(|| {
            names.push(t.clone());
            names.len() - 1
        })
    }

    /// The terms `vc` uses as lists, and what they are made of: a `car`'s
    /// or a `cdr`'s, one tested `nil`, a list argument of a function
    /// defined, a pair `cons` made and its parts; until no more are found.
    /// Each of the sort its type gives, or a list's tail, or its element.
    fn lists_of(&mut self, vc: &Formula<Term>) {
        let mut terms = Vec::new();
        formula_terms(vc, &mut terms);
        loop {
            let before = self.list.len();
            let mut found = Vec::new();
            for t in &terms {
                list_uses(t, &self.cx, &mut found);
            }
            // What a pair is made of: its tail a list of its sort, its head
            // of its elements'.
            let mut parts = Vec::new();
            for (m, a, d) in self.cx.conses {
                let Some(l) = self.sort_in(m).or_else(|| self.finite(m)) else { continue };
                found.push(m.clone());
                parts.push((d.clone(), l.clone()));
                if let Some(e @ Sort::List(_)) = l.elem() {
                    parts.push((a.clone(), e.clone()));
                }
                terms.push(d.clone());
            }
            // Of a finite list only: the solver's are finite, and would
            // prove of a cycle what does not hold of it.
            for f in found {
                if let Some(l) = self.finite(&f).or_else(|| self.part(&f)) {
                    self.note(f, l);
                }
            }
            for (f, l) in parts {
                self.note(f, l);
            }
            if self.list.len() == before {
                break;
            }
        }
    }

    /// `t` noted a list of sort `l`, unless it is `nil` or is already.
    fn note(&mut self, t: Term, l: Sort) {
        if !is_nil(&t) && self.sort_in(&t).is_none() {
            self.list.push((t, l));
        }
    }

    /// `t`'s sort, if its type says it is a finite list.
    fn finite(&self, t: &Term) -> Option<Sort> {
        self.cx.finite.iter().find(|(f, _)| f == t).map(|(_, l)| l.clone())
    }

    /// `t`'s sort, if it is noted a list.
    fn sort_in(&self, t: &Term) -> Option<Sort> {
        self.list.iter().find(|(f, _)| f == t).map(|(_, l)| l.clone())
    }

    /// `t`'s sort, if it is a part of a list noted one: its tail (of its
    /// sort), its head (of its elements', if a list's).
    fn part(&self, t: &Term) -> Option<Sort> {
        match t {
            Term::App("cdr", xs) if xs.len() == 1 => self.sort_in(&xs[0]),
            Term::App("car", xs) if xs.len() == 1 => self.sort_in(&xs[0])?.elem().filter(|e| e.elem().is_some()).cloned(),
            _ => None,
        }
    }

    /// Whether `t` is a list of sort `l` (or `nil`, of any).
    fn fits(&self, t: &Term, l: &Sort) -> bool {
        is_nil(t) || self.sort_in(t).as_ref() == Some(l)
    }

    /// `t`, a list of sort `l` (`fits`): `nil`, a tail, a head, or a
    /// constant.
    fn list_term(&mut self, t: &Term, l: &Sort) -> String {
        match t {
            _ if is_nil(t) => l.nil(),
            Term::App(f @ ("car" | "cdr"), xs) if xs.len() == 1 && let Some(m) = self.sort_in(&xs[0]) => {
                format!("({} {})", if *f == "car" { "hd" } else { "tl" }, self.list_term(&xs[0], &m))
            }
            _ => match self.lists.iter().position(|(n, _)| n == t) {
                Some(k) => format!("l{k}"),
                None => {
                    self.lists.push((t.clone(), l.clone()));
                    format!("l{}", self.lists.len() - 1)
                }
            },
        }
    }

    /// `t` as an element of sort `e`, if it can be one.
    fn element(&mut self, t: &Term, e: &Sort) -> Option<String> {
        match e {
            Sort::Int => Some(self.expr(&crate::typed_cells::expr_of(t))),
            Sort::Bool => Some(self.formula(&Formula::Holds(t.clone()))),
            Sort::List(_) => self.fits(t, e).then(|| self.list_term(t, e)),
        }
    }

    /// `(car x)`, of a list noted one whose elements are of sort `e`.
    fn head(&self, t: &Term, e: &Sort) -> Option<Term> {
        match t {
            Term::App("car", xs) if xs.len() == 1 && self.sort_in(&xs[0]).as_ref().and_then(|l| l.elem()) == Some(e) => Some(xs[0].clone()),
            _ => None,
        }
    }

    /// `f` applied to `xs`: as defined, if it is; else uninterpreted, of a
    /// `Bool` (`b`) or an `Int`.
    fn call(&mut self, f: &Rc<str>, xs: &[Term], b: bool) -> String {
        if let Some((ps, r)) = self.cx.signature(f)
            && ps.len() == xs.len()
            && (r == Sort::Bool) == b
            && ps.iter().zip(xs).all(|(p, x)| p.elem().is_none() || self.fits(x, p))
        {
            let ps = ps.to_vec();
            let xs: Vec<String> = ps.iter().zip(xs).map(|(p, x)| self.element(x, p).expect("fits")).collect();
            return if xs.is_empty() { symbol(f) } else { format!("({} {})", symbol(f), xs.join(" ")) };
        }
        let k = self.funs.iter().position(|(g, n, c)| g == f && *n == xs.len() && *c == b).unwrap_or_else(|| {
            self.funs.push((f.clone(), xs.len(), b));
            self.funs.len() - 1
        });
        if xs.is_empty() {
            return format!("f{k}");
        }
        let xs: Vec<String> = xs.iter().map(|x| self.expr(&crate::typed_cells::expr_of(x))).collect();
        format!("(f{k} {})", xs.join(" "))
    }

    fn expr(&mut self, e: &Expr<Term>) -> String {
        match e {
            Expr::Atom(Term::Lit(v)) if v.is_fixnum() => int(v.as_fixnum() as i128),
            Expr::Atom(Term::Call(f, xs)) => self.call(f, xs, false),
            Expr::Atom(t) if let Some(l) = self.head(t, &Sort::Int) => {
                let l = self.sort_in(&l).map(|s| self.list_term(&l, &s)).expect("noted");
                format!("(hd {l})")
            }
            Expr::Atom(t) => format!("i{}", Self::named(&mut self.ints, t)),
            Expr::Lit(k) => int(*k as i128),
            Expr::Add(x, y) => format!("(+ {} {})", self.expr(x), self.expr(y)),
            Expr::Sub(x, y) => format!("(- {} {})", self.expr(x), self.expr(y)),
            Expr::Mul(x, y) => format!("(* {} {})", self.expr(x), self.expr(y)),
        }
    }

    fn formula(&mut self, f: &Formula<Term>) -> String {
        use crate::ast::Rel;
        let all = |w: &mut Self, op: &str, unit: &str, fs: &[Formula<Term>]| match fs {
            [] => unit.to_string(),
            [f] => w.formula(f),
            fs => format!("({op} {})", fs.iter().map(|f| w.formula(f)).collect::<Vec<_>>().join(" ")),
        };
        match f {
            Formula::True => "true".into(),
            Formula::False => "false".into(),
            Formula::Rel(r, x, y) => {
                let (x, y) = (self.expr(x), self.expr(y));
                match r {
                    Rel::Lt => format!("(< {x} {y})"),
                    Rel::Le => format!("(<= {x} {y})"),
                    Rel::Eq => format!("(= {x} {y})"),
                    Rel::Ne => format!("(not (= {x} {y}))"),
                }
            }
            Formula::Holds(Term::Lit(v)) if v.is_false() => "false".into(),
            Formula::Holds(Term::Lit(v)) if *v == fixpt_heap::Value::TRUE => "true".into(),
            Formula::Holds(Term::Call(f, xs)) => self.call(f, xs, true),
            // Two lists the same: the same list, while nothing writes.
            Formula::Holds(Term::App("eq", xs))
                if xs.len() == 2
                    && let Some(l) = self.sort_in(&xs[0]).or_else(|| self.sort_in(&xs[1]))
                    && xs.iter().all(|x| self.fits(x, &l)) =>
            {
                format!("(= {} {})", self.list_term(&xs[0], &l), self.list_term(&xs[1], &l))
            }
            Formula::Holds(t) if let Some(l) = self.head(t, &Sort::Bool) => {
                let l = self.sort_in(&l).map(|s| self.list_term(&l, &s)).expect("noted");
                format!("(hd {l})")
            }
            Formula::Holds(t) => format!("b{}", Self::named(&mut self.bools, t)),
            Formula::Not(p) => format!("(not {})", self.formula(p)),
            Formula::And(ps) => all(self, "and", "true", ps),
            Formula::Or(ps) => all(self, "or", "false", ps),
            Formula::Implies(p, q) => format!("(=> {} {})", self.formula(p), self.formula(q)),
        }
    }
}

/// Every term of `f`, as it stands (not the terms inside them).
fn formula_terms(f: &Formula<Term>, out: &mut Vec<Term>) {
    fn expr(e: &Expr<Term>, out: &mut Vec<Term>) {
        match e {
            Expr::Atom(t) => out.push(t.clone()),
            Expr::Lit(_) => {}
            Expr::Add(x, y) | Expr::Sub(x, y) | Expr::Mul(x, y) => {
                expr(x, out);
                expr(y, out);
            }
        }
    }
    match f {
        Formula::True | Formula::False => {}
        Formula::Rel(_, x, y) => {
            expr(x, out);
            expr(y, out);
        }
        Formula::Holds(t) => out.push(t.clone()),
        Formula::Not(p) => formula_terms(p, out),
        Formula::And(ps) | Formula::Or(ps) => ps.iter().for_each(|p| formula_terms(p, out)),
        Formula::Implies(p, q) => {
            formula_terms(p, out);
            formula_terms(q, out);
        }
    }
}

/// The terms `t`, and those inside it, use as lists, onto `out`.
fn list_uses(t: &Term, th: &Context, out: &mut Vec<Term>) {
    match t {
        Term::App(f @ ("car" | "cdr"), xs) if xs.len() == 1 => {
            out.push(xs[0].clone());
            if *f == "cdr" {
                out.push(t.clone());
            }
            list_uses(&xs[0], th, out);
        }
        Term::App("eq", xs) if xs.len() == 2 => {
            if is_nil(&xs[1]) {
                out.push(xs[0].clone());
            }
            if is_nil(&xs[0]) {
                out.push(xs[1].clone());
            }
            xs.iter().for_each(|x| list_uses(x, th, out));
        }
        Term::Call(f, xs) => {
            if let Some((ps, _)) = th.signature(f) {
                for (p, x) in ps.iter().zip(xs) {
                    if p.elem().is_some() {
                        out.push(x.clone());
                    }
                }
            }
            xs.iter().for_each(|x| list_uses(x, th, out));
        }
        Term::App(_, xs) => xs.iter().for_each(|x| list_uses(x, th, out)),
        _ => {}
    }
}

pub(crate) fn int(k: i128) -> String {
    if k < 0 { format!("(- {})", -k) } else { k.to_string() }
}

/// An s-expression of the solver's answer.
#[derive(Debug)]
enum Sx {
    Atom(String),
    List(Vec<Sx>),
}

fn read_sxs(toks: &[String], i: &mut usize) -> Vec<Sx> {
    let mut out = Vec::new();
    while *i < toks.len() {
        match toks[*i].as_str() {
            "(" => {
                *i += 1;
                out.push(Sx::List(read_sxs(toks, i)));
            }
            ")" => {
                *i += 1;
                return out;
            }
            a => {
                *i += 1;
                out.push(Sx::Atom(a.to_string()));
            }
        }
    }
    out
}

/// `x` as a value: an integer (`5`, `(- 3)`), a boolean, a list (`nil`,
/// `(as nil (List Int))`, `(cons 1 (cons 2 nil))`) of values.
fn value(x: &Sx) -> Option<Val> {
    fn integer(x: &Sx) -> Option<i128> {
        match x {
            Sx::Atom(k) => k.parse().ok(),
            Sx::List(xs) => match &xs[..] {
                [Sx::Atom(m), k] if m == "-" => integer(k).map(|k| -k),
                _ => None,
            },
        }
    }
    fn list(x: &Sx) -> Option<Vec<Val>> {
        match x {
            Sx::Atom(n) if n == "nil" => Some(Vec::new()),
            Sx::List(xs) => match &xs[..] {
                [Sx::Atom(a), Sx::Atom(n), _] if a == "as" && n == "nil" => Some(Vec::new()),
                [Sx::Atom(c), h, t] if c == "cons" => {
                    let mut rest = list(t)?;
                    rest.insert(0, value(h)?);
                    Some(rest)
                }
                _ => None,
            },
            _ => None,
        }
    }
    match x {
        Sx::Atom(b) if b == "true" => Some(Val::Bool(true)),
        Sx::Atom(b) if b == "false" => Some(Val::Bool(false)),
        _ => integer(x).map(Val::Int).or_else(|| list(x).map(Val::List)),
    }
}

/// The values of a `get-value` answer, `((i0 5) (i1 (- 3)) (b0 true) (l0
/// (cons 1 nil)))`, by name.
fn values(s: &str) -> Vec<(String, Val)> {
    let toks: Vec<String> = s.replace('(', " ( ").replace(')', " ) ").split_whitespace().map(String::from).collect();
    let mut i = 0;
    let sxs = read_sxs(&toks, &mut i);
    let mut out = Vec::new();
    for top in &sxs {
        let Sx::List(pairs) = top else { continue };
        for p in pairs {
            if let Sx::List(nv) = p
                && let [Sx::Atom(n), v] = &nv[..]
                && n.len() > 1
                && n.starts_with(['i', 'b', 'l'])
                && n[1..].parse::<usize>().is_ok()
                && let Some(v) = value(v)
            {
                out.push((n.clone(), v));
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn values_are_read() {
        let v = values("((i0 5) (i1 (- 3)) (b0 true) (l0 (cons 1 (cons (- 2) nil))) (l1 nil))");
        assert_eq!(
            v,
            vec![
                ("i0".into(), Val::Int(5)),
                ("i1".into(), Val::Int(-3)),
                ("b0".into(), Val::Bool(true)),
                ("l0".into(), Val::List(vec![Val::Int(1), Val::Int(-2)])),
                ("l1".into(), Val::List(vec![]))
            ]
        );
        // A list of lists, its `nil`s of their sorts; of booleans.
        let v = values("((l0 (cons (as nil (List Int)) (cons (cons 3 (as nil (List Int))) (as nil (List (List Int)))))) (l1 (cons true (as nil (List Bool)))))");
        let ints = |xs: &[i128]| Val::List(xs.iter().map(|x| Val::Int(*x)).collect());
        assert_eq!(v, vec![("l0".into(), Val::List(vec![ints(&[]), ints(&[3])])), ("l1".into(), Val::List(vec![Val::Bool(true)]))]);
        assert_eq!(v[0].1.printed(), "(() (3))");
    }

    /// With a solver, a true VC proved, a false one refuted by values that
    /// deny it; `x * x ≥ 0`, beyond the logic's own prover, proved.
    #[test]
    fn a_solver_proves_and_refutes() {
        let Some(z3) = solver() else { return };
        let x = || Expr::Atom(Term::Slot(0));
        let sq = Formula::Rel(crate::ast::Rel::Le, Expr::Lit(0), Expr::Mul(Box::new(x()), Box::new(x())));
        assert!(matches!(solve(&z3, &sq, Context::default()), Solved::Proved));
        let pos = Formula::Rel(crate::ast::Rel::Lt, Expr::Lit(0), x());
        match solve(&z3, &pos, Context::default()) {
            Solved::Refuted(m) => assert!(matches!(m[..], [(Term::Slot(0), Val::Int(k))] if k <= 0), "{m:?}"),
            other => panic!("{other:?}"),
        }
    }
}
