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
//! A logic function's call (`Term::Call`) is an uninterpreted function
//! applied, of a `Bool` or an `Int` by where it stands, its arguments
//! integers (a value not an integer is a constant all the same: the
//! solver compares, and nothing else, as congruence asks).
//!
//! The solver is z3, run as `z3 -in`, or what `FIXPT_SMT` names; none, and
//! nothing is asked.

use crate::logic::{Expr, Formula};
use crate::typed_cells::Term;
use std::io::Write;
use std::process::{Command, Stdio};

/// A value the solver gave a term.
#[derive(Clone, Debug, PartialEq)]
pub enum Val {
    Int(i128),
    Bool(bool),
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

/// The solver's command, if there is one: `FIXPT_SMT`, else `z3` where it
/// runs.
pub fn solver() -> Option<String> {
    let cmd = std::env::var("FIXPT_SMT").unwrap_or_else(|_| "z3".into());
    let runs = Command::new(&cmd).arg("-version").stdout(Stdio::null()).stderr(Stdio::null()).status();
    runs.is_ok_and(|s| s.success()).then_some(cmd)
}

/// How long the solver is given for one VC, in milliseconds.
const TIMEOUT_MS: u32 = 2000;

/// `vc` asked of `solver`.
pub fn solve(solver: &str, vc: &Formula<Term>) -> Solved {
    let mut w = Writer::default();
    let denied = format!("(not {})", w.formula(vc));
    let mut q = String::from("(set-option :produce-models true)\n(set-logic ALL)\n");
    for (i, _) in w.ints.iter().enumerate() {
        q += &format!("(declare-const i{i} Int)\n");
    }
    for (i, _) in w.bools.iter().enumerate() {
        q += &format!("(declare-const b{i} Bool)\n");
    }
    for (i, (_, n, b)) in w.funs.iter().enumerate() {
        q += &format!("(declare-fun f{i} ({}) {})\n", vec!["Int"; *n].join(" "), if *b { "Bool" } else { "Int" });
    }
    q += &format!("(assert {denied})\n(check-sat)\n");
    let names: Vec<String> = (0..w.ints.len()).map(|i| format!("i{i}")).chain((0..w.bools.len()).map(|i| format!("b{i}"))).collect();
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
            let vals = values(&rest);
            let model = vals.into_iter().filter_map(|(n, v)| {
                let k: usize = n[1..].parse().ok()?;
                let t = if n.starts_with('i') { w.ints.get(k) } else { w.bools.get(k) };
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

/// The terms named so far, an integer's and a boolean's, by number.
#[derive(Default)]
struct Writer {
    ints: Vec<Term>,
    bools: Vec<Term>,
    /// The functions called: each one's name, how many arguments, and
    /// whether of a `Bool`.
    funs: Vec<(std::rc::Rc<str>, usize, bool)>,
}

impl Writer {
    fn named(names: &mut Vec<Term>, t: &Term) -> usize {
        names.iter().position(|n| n == t).unwrap_or_else(|| {
            names.push(t.clone());
            names.len() - 1
        })
    }

    /// `f` applied to `xs`, of a `Bool` (`b`) or an `Int`.
    fn call(&mut self, f: &std::rc::Rc<str>, xs: &[Term], b: bool) -> String {
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
            Formula::Holds(t) => format!("b{}", Self::named(&mut self.bools, t)),
            Formula::Not(p) => format!("(not {})", self.formula(p)),
            Formula::And(ps) => all(self, "and", "true", ps),
            Formula::Or(ps) => all(self, "or", "false", ps),
            Formula::Implies(p, q) => format!("(=> {} {})", self.formula(p), self.formula(q)),
        }
    }
}

fn int(k: i128) -> String {
    if k < 0 { format!("(- {})", -k) } else { k.to_string() }
}

/// The values of a `get-value` answer, `((i0 5) (i1 (- 3)) (b0 true))`, by
/// name.
fn values(s: &str) -> Vec<(String, Val)> {
    let toks: Vec<String> = s.replace('(', " ( ").replace(')', " ) ").split_whitespace().map(String::from).collect();
    let mut out = Vec::new();
    let mut i = 0;
    while i < toks.len() {
        // `( NAME VALUE )`, VALUE an atom or `( - K )`.
        if toks[i] == "(" && toks.get(i + 1).is_some_and(|n| n.starts_with(['i', 'b']) && n[1..].parse::<usize>().is_ok()) {
            let name = toks[i + 1].clone();
            let (v, next) = match toks.get(i + 2).map(String::as_str) {
                Some("(") if toks.get(i + 3).map(String::as_str) == Some("-") => (toks.get(i + 4).and_then(|k| k.parse::<i128>().ok()).map(|k| Val::Int(-k)), i + 6),
                Some("true") => (Some(Val::Bool(true)), i + 3),
                Some("false") => (Some(Val::Bool(false)), i + 3),
                Some(k) => (k.parse::<i128>().ok().map(Val::Int), i + 3),
                None => (None, i + 2),
            };
            if let Some(v) = v {
                out.push((name, v));
            }
            i = next;
        } else {
            i += 1;
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn values_are_read() {
        let v = values("((i0 5) (i1 (- 3)) (b0 true))");
        assert_eq!(v, vec![("i0".into(), Val::Int(5)), ("i1".into(), Val::Int(-3)), ("b0".into(), Val::Bool(true))]);
    }

    /// With a solver, a true VC proved, a false one refuted by values that
    /// deny it; `x * x ≥ 0`, beyond the logic's own prover, proved.
    #[test]
    fn a_solver_proves_and_refutes() {
        let Some(z3) = solver() else { return };
        let x = || Expr::Atom(Term::Slot(0));
        let sq = Formula::Rel(crate::ast::Rel::Le, Expr::Lit(0), Expr::Mul(Box::new(x()), Box::new(x())));
        assert!(matches!(solve(&z3, &sq), Solved::Proved));
        let pos = Formula::Rel(crate::ast::Rel::Lt, Expr::Lit(0), x());
        match solve(&z3, &pos) {
            Solved::Refuted(m) => assert!(matches!(m[..], [(Term::Slot(0), Val::Int(k))] if k <= 0), "{m:?}"),
            other => panic!("{other:?}"),
        }
    }
}
