//! The logic functions' definitions, for the SMT solver
//! (`docs/research/specs-and-counterexamples.md`, S4, §5 and §6): each a
//! `define-fun-rec` of its body, over integers, booleans and lists of
//! integers (a datatype, `L`), so that the solver unfolds what it
//! computes.
//!
//! A body is defined only if all of it is of what is translated: `if`
//! (so `and`, `or`, `cond`), `null?`, `pair?`, `car` and `cdr` of a list a
//! test has shown a pair, `cons`, integer arithmetic and comparisons,
//! `not`, its parameters, `nil`, literals, and calls of itself or of the
//! logic functions defined before it. Anything else, and it is left
//! undefined, a function the solver knows nothing of but that it is one.
//! A `car` or `cdr` only where its list is a pair keeps a definition total,
//! as the function is: its equations say what a run gives, where it ends,
//! which `pure` says it does (the checkers' size-change check).

use crate::ast::{Exp, ExpId, Ty, TyId};
use crate::{Checker, Top};
use fixpt_read::Sym;
use std::rc::Rc;

/// A sort of the solver's: an integer, a boolean, a list of integers.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Sort {
    Int,
    Bool,
    List,
}

impl Sort {
    pub fn name(self) -> &'static str {
        match self {
            Sort::Int => "Int",
            Sort::Bool => "Bool",
            Sort::List => "L",
        }
    }
}

/// The lists of integers, as the solver has them.
pub const LISTS: &str = "(declare-datatypes ((L 0)) (((nil) (cons (hd Int) (tl L)))))";

/// The logic functions defined: each one's name, its parameters' sorts and
/// its result's; and their definitions, in order.
#[derive(Clone, Debug, Default)]
pub struct Theory {
    pub defined: Vec<(Rc<str>, Vec<Sort>, Sort)>,
    pub definitions: Vec<String>,
}

impl Theory {
    /// The logic functions of a program the checker `c` checked to `tops`.
    pub fn of(c: &Checker, tops: &[Top]) -> Theory {
        let mut th = Theory::default();
        for t in tops {
            let Top::Define { name, ty, exp, .. } = t else { continue };
            if let Some(d) = th.define(c, *name, *ty, *exp) {
                th.definitions.push(d);
            }
        }
        th
    }

    /// `f`'s parameters' sorts and its result's, if it is defined.
    pub fn signature(&self, f: &str) -> Option<(&[Sort], Sort)> {
        self.defined.iter().find(|(g, ..)| &**g == f).map(|(_, ps, r)| (&ps[..], *r))
    }

    /// What the solver is told first: the lists, and the definitions.
    pub fn prelude(&self) -> String {
        let mut out = format!("{LISTS}\n");
        for d in &self.definitions {
            out += d;
            out.push('\n');
        }
        out
    }

    /// The definition of `name`, of type `ty`, bound to `exp`, if it is a
    /// logic function whose body is translated; it noted defined.
    fn define(&mut self, c: &Checker, name: Sym, ty: TyId, exp: ExpId) -> Option<String> {
        let Ty::Subr { effect, params, result, .. } = c.arena.get(c.arena.resolve(ty)).clone() else { return None };
        if !effect.is_pure() {
            return None;
        }
        let sorts = params.iter().map(|p| sort_of(c, *p)).collect::<Option<Vec<_>>>()?;
        let result = match sort_of(c, result)? {
            Sort::List => return None,
            s => s,
        };
        let (ps, body, selves) = lambda_of(c, exp)?;
        if ps.len() != sorts.len() {
            return None;
        }
        let fname: Rc<str> = c.name(name).into();
        // Defined while its body is read, for its calls of itself.
        self.defined.push((fname.clone(), sorts.clone(), result));
        let tr = Translator { c, th: self, params: ps.iter().zip(&sorts).enumerate().map(|(i, (p, s))| (*p, format!("p{i}"), *s)).collect(), selves, name, fname: fname.clone() };
        match tr.exp(body, &[]) {
            Some((b, s)) if s == result => {
                let ps: Vec<String> = sorts.iter().enumerate().map(|(i, s)| format!("(p{i} {})", s.name())).collect();
                Some(format!("(define-fun-rec |{fname}| ({}) {} {b})", ps.join(" "), result.name()))
            }
            _ => {
                self.defined.pop();
                None
            }
        }
    }
}

/// `t`'s sort, if it has one: an `int` or `nat`, a `bool`, a finite list
/// of `int`s that nothing writes (`(listof int acyclic)`).
pub fn sort_of(c: &Checker, t: TyId) -> Option<Sort> {
    let t = c.arena.resolve(t);
    if c.is_int(t) {
        return Some(Sort::Int);
    }
    if c.is_bool(t) {
        return Some(Sort::Bool);
    }
    match c.arena.get(t) {
        // Finite, never written: the solver's lists are all finite.
        Ty::Pair(e, tail, crate::ast::Region::Frozen(_, true), true) if c.arena.resolve(*tail) == t && c.arena.resolve(*e) == c.int => Some(Sort::List),
        _ => None,
    }
}

/// `exp`'s `lambda`: its parameters, its body, and the names it calls
/// itself by (a `letrec`'s, of `(letrec ((s T (lambda …))) s)`).
fn lambda_of(c: &Checker, exp: ExpId) -> Option<(Vec<Sym>, ExpId, Vec<Sym>)> {
    match c.arena.exp_at(exp) {
        Exp::Lambda { params, body } => Some((params.iter().map(|(p, _)| *p).collect(), *body, Vec::new())),
        Exp::The { exp, .. } => lambda_of(c, *exp),
        Exp::Letrec { bindings, body } if bindings.len() == 1 && matches!(c.arena.exp_at(*body), Exp::Var(s) if *s == bindings[0].0) => {
            let (ps, b, mut selves) = lambda_of(c, bindings[0].2)?;
            selves.push(bindings[0].0);
            Some((ps, b, selves))
        }
        _ => None,
    }
}

struct Translator<'a> {
    c: &'a Checker,
    th: &'a Theory,
    params: Vec<(Sym, String, Sort)>,
    selves: Vec<Sym>,
    name: Sym,
    fname: Rc<str>,
}

impl Translator<'_> {
    /// `e` as the solver's term, and its sort; `pairs`, the lists a test
    /// has shown pairs where it is.
    fn exp(&self, e: ExpId, pairs: &[String]) -> Option<(String, Sort)> {
        match self.c.arena.exp_at(e) {
            Exp::Var(x) => match self.params.iter().find(|(p, ..)| p == x) {
                Some((_, n, s)) => Some((n.clone(), *s)),
                None if self.c.name(*x) == "nil" => Some(("nil".into(), Sort::List)),
                None => None,
            },
            Exp::Int(k) => Some((crate::smt::int(*k as i128), Sort::Int)),
            Exp::Bool(b) => Some((b.to_string(), Sort::Bool)),
            Exp::The { exp, .. } => self.exp(*exp, pairs),
            Exp::If { test, then, els } => {
                let (t, ts) = self.exp(*test, pairs)?;
                if ts != Sort::Bool {
                    return None;
                }
                let (yes, no) = self.shown(*test, pairs);
                let (a, sa) = self.exp(*then, &yes)?;
                let (b, sb) = self.exp(*els, &no)?;
                (sa == sb).then(|| (format!("(ite {t} {a} {b})"), sa))
            }
            Exp::App { fun, args } => {
                let Exp::Var(f) = self.c.arena.exp_at(*fun) else { return None };
                // A parameter is no function.
                if self.params.iter().any(|(p, ..)| p == f) {
                    return None;
                }
                let xs = args.iter().map(|a| self.exp(*a, pairs)).collect::<Option<Vec<_>>>()?;
                let called = if *f == self.name || self.selves.contains(f) { Some(self.fname.clone()) } else { Some(Rc::from(self.c.name(*f))) };
                let called = called.filter(|g| self.th.signature(g).is_some() && (*f == self.name || self.selves.contains(f) || self.c.global_type(*f).is_some()));
                if let Some(g) = called {
                    let (ps, r) = self.th.signature(&g)?;
                    if ps.len() != xs.len() || ps.iter().zip(&xs).any(|(p, (_, s))| p != s) {
                        return None;
                    }
                    let xs: Vec<&str> = xs.iter().map(|(x, _)| x.as_str()).collect();
                    return Some((format!("(|{g}| {})", xs.join(" ")), r));
                }
                self.standard(self.c.name(*f), &xs, pairs)
            }
            _ => None,
        }
    }

    /// A standard procedure's call, of what the solver has.
    fn standard(&self, f: &str, xs: &[(String, Sort)], pairs: &[String]) -> Option<(String, Sort)> {
        use Sort::*;
        let sorts: Vec<Sort> = xs.iter().map(|(_, s)| *s).collect();
        let x = |i: usize| xs[i].0.as_str();
        Some(match (f, &sorts[..]) {
            ("null?", [List]) => (format!("(= {} nil)", x(0)), Bool),
            ("pair?", [List]) => (format!("(not (= {} nil))", x(0)), Bool),
            ("car", [List]) if pairs.iter().any(|p| p == x(0)) => (format!("(hd {})", x(0)), Int),
            ("cdr", [List]) if pairs.iter().any(|p| p == x(0)) => (format!("(tl {})", x(0)), List),
            ("cons", [Int, List]) => (format!("(cons {} {})", x(0), x(1)), List),
            ("+" | "-" | "*", [Int, Int]) => (format!("({f} {} {})", x(0), x(1)), Int),
            ("-", [Int]) => (format!("(- {})", x(0)), Int),
            ("<" | "<=" | "=" | ">" | ">=", [Int, Int]) => (format!("({f} {} {})", x(0), x(1)), Bool),
            ("not", [Bool]) => (format!("(not {})", x(0)), Bool),
            _ => return None,
        })
    }

    /// The lists `test` shows pairs where it is true, and where false, with
    /// those `pairs` already has: `(null? x)` false, `(pair? x)` true, and
    /// `not` of one, the other way.
    fn shown(&self, test: ExpId, pairs: &[String]) -> (Vec<String>, Vec<String>) {
        let (mut yes, mut no) = (pairs.to_vec(), pairs.to_vec());
        let mut test = test;
        let mut flip = false;
        loop {
            let Exp::App { fun, args } = self.c.arena.exp_at(test) else { break };
            let Exp::Var(f) = self.c.arena.exp_at(*fun) else { break };
            let f = self.c.name(*f);
            match (f, &args[..]) {
                ("not", [a]) => {
                    test = *a;
                    flip = !flip;
                }
                ("null?" | "pair?", [a]) => {
                    if let Some((x, Sort::List)) = self.exp(*a, pairs) {
                        let into_yes = (f == "pair?") != flip;
                        if into_yes { yes.push(x) } else { no.push(x) }
                    }
                    break;
                }
                _ => break,
            }
        }
        (yes, no)
    }
}
