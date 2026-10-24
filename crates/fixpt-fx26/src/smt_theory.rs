//! The logic functions' definitions, for the SMT solver
//! (`docs/research/specs-and-counterexamples.md`, S4, §5 and §6): each a
//! `define-fun-rec` of its body, over integers, booleans and lists of
//! any of these (a datatype, `(List T)`, of its elements' sort `T`), so
//! that the solver unfolds what it computes.
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

/// A sort of the solver's: an integer, a boolean, a list of a sort's.
#[derive(Clone, Debug, PartialEq)]
pub enum Sort {
    Int,
    Bool,
    List(Rc<Sort>),
}

impl Sort {
    pub fn name(&self) -> String {
        match self {
            Sort::Int => "Int".into(),
            Sort::Bool => "Bool".into(),
            Sort::List(e) => format!("(List {})", e.name()),
        }
    }

    /// Its elements' sort, if it is a list's.
    pub fn elem(&self) -> Option<&Sort> {
        match self {
            Sort::List(e) => Some(e),
            _ => None,
        }
    }

    /// `nil` of this sort, a list's: `(as nil (List Int))`, as the solver
    /// asks of a constructor of a sort with a parameter.
    pub fn nil(&self) -> String {
        format!("(as nil {})", self.name())
    }
}

/// The lists, as the solver has them: of a sort `T`, for any `T`.
pub const LISTS: &str = "(declare-datatypes ((List 1)) ((par (T) ((nil) (cons (hd T) (tl (List T)))))))";

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
        self.defined.iter().find(|(g, ..)| &**g == f).map(|(_, ps, r)| (&ps[..], r.clone()))
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
            Sort::List(_) => return None,
            s => s,
        };
        let (ps, body, selves) = lambda_of(c, exp)?;
        if ps.len() != sorts.len() {
            return None;
        }
        let fname: Rc<str> = c.name(name).into();
        // Defined while its body is read, for its calls of itself.
        self.defined.push((fname.clone(), sorts.clone(), result.clone()));
        let tr = Translator { c, th: self, params: ps.iter().zip(&sorts).enumerate().map(|(i, (p, s))| (*p, format!("p{i}"), s.clone())).collect(), selves, name, fname: fname.clone() };
        match tr.exp(body, Some(&result), &[]) {
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
/// that nothing writes (`(listof T acyclic)`, a `nlist`) of elements each
/// an `int`, a `bool` or a list so (`exact`).
pub fn sort_of(c: &Checker, t: TyId) -> Option<Sort> {
    if c.is_int(t) { Some(Sort::Int) } else { exact(c, t) }
}

/// `t`'s sort, as `sort_of`, but no `nat`, as the solver's `Int` is any
/// integer: a list it gave of one would be none of the type's. (Nor is a
/// `nlist`'s size said; a list of another length, a replay finds none.)
fn exact(c: &Checker, t: TyId) -> Option<Sort> {
    let t = c.arena.resolve(t);
    if t == c.int {
        return Some(Sort::Int);
    }
    if c.is_bool(t) {
        return Some(Sort::Bool);
    }
    let list = |e: TyId| exact(c, e).map(|e| Sort::List(Rc::new(e)));
    match c.arena.get(t) {
        // Finite, never written: the solver's lists are all finite. A pair
        // (never `nil`) with such a tail, a list of the tail's sort.
        Ty::Pair(e, tail, crate::ast::Region::Frozen(_, true), _) => {
            let l = list(*e)?;
            (c.arena.resolve(*tail) == t || exact(c, *tail).as_ref() == Some(&l)).then_some(l)
        }
        Ty::NList { elem, region: crate::ast::Region::Frozen(_, true), .. } => list(*elem),
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
    /// `e` as the solver's term, and its sort; `want`, the sort it is to
    /// have, if that is known (for `nil`, of whatever list's); `pairs`, the
    /// lists a test has shown pairs where it is.
    fn exp(&self, e: ExpId, want: Option<&Sort>, pairs: &[String]) -> Option<(String, Sort)> {
        match self.c.arena.exp_at(e) {
            Exp::Var(x) => match self.params.iter().find(|(p, ..)| p == x) {
                Some((_, n, s)) => Some((n.clone(), s.clone())),
                None if self.c.name(*x) == "nil" => want.filter(|w| w.elem().is_some()).map(|w| (w.nil(), w.clone())),
                None => None,
            },
            Exp::Int(k) => Some((crate::smt::int(*k as i128), Sort::Int)),
            Exp::Bool(b) => Some((b.to_string(), Sort::Bool)),
            Exp::The { exp, .. } => self.exp(*exp, want, pairs),
            Exp::If { test, then, els } => {
                let (t, _) = self.exp(*test, Some(&Sort::Bool), pairs).filter(|(_, s)| *s == Sort::Bool)?;
                let (yes, no) = self.shown(*test, pairs);
                // A branch's sort the other's, where it is wanted (a `nil`).
                let (a, b) = match self.exp(*then, want, &yes) {
                    Some(a) => {
                        let b = self.exp(*els, Some(&a.1), &no)?;
                        (a, b)
                    }
                    None if want.is_none() => {
                        let b = self.exp(*els, None, &no)?;
                        (self.exp(*then, Some(&b.1), &yes)?, b)
                    }
                    None => return None,
                };
                (a.1 == b.1).then(|| (format!("(ite {t} {} {})", a.0, b.0), a.1))
            }
            Exp::App { fun, args } => {
                let Exp::Var(f) = self.c.arena.exp_at(*fun) else { return None };
                // A parameter is no function.
                if self.params.iter().any(|(p, ..)| p == f) {
                    return None;
                }
                let itself = *f == self.name || self.selves.contains(f);
                let g: Rc<str> = if itself { self.fname.clone() } else { Rc::from(self.c.name(*f)) };
                if (itself || self.c.global_type(*f).is_some())
                    && let Some((ps, r)) = self.th.signature(&g)
                {
                    if ps.len() != args.len() {
                        return None;
                    }
                    let mut xs = Vec::new();
                    for (p, a) in ps.iter().zip(args.iter()) {
                        let (x, s) = self.exp(*a, Some(p), pairs)?;
                        if s != *p {
                            return None;
                        }
                        xs.push(x);
                    }
                    return Some((format!("(|{g}| {})", xs.join(" ")), r));
                }
                // `cons`'s tail, a list of its head's sort.
                let mut xs: Vec<(String, Sort)> = Vec::new();
                for a in args.iter() {
                    let want = match (self.c.name(*f), &xs[..]) {
                        ("cons", [(_, h)]) => Some(Sort::List(Rc::new(h.clone()))),
                        _ => None,
                    };
                    xs.push(self.exp(*a, want.as_ref(), pairs)?);
                }
                self.standard(self.c.name(*f), &xs, pairs)
            }
            _ => None,
        }
    }

    /// A standard procedure's call, of what the solver has.
    fn standard(&self, f: &str, xs: &[(String, Sort)], pairs: &[String]) -> Option<(String, Sort)> {
        use Sort::*;
        let x = |i: usize| xs[i].0.as_str();
        let pair = |i: usize| pairs.iter().any(|p| p == x(i));
        let sorts: Vec<&Sort> = xs.iter().map(|(_, s)| s).collect();
        Some(match (f, &sorts[..]) {
            ("null?", [l @ List(_)]) => (format!("(= {} {})", x(0), l.nil()), Bool),
            ("pair?", [l @ List(_)]) => (format!("(not (= {} {}))", x(0), l.nil()), Bool),
            ("car", [List(e)]) if pair(0) => (format!("(hd {})", x(0)), (**e).clone()),
            ("cdr", [l @ List(_)]) if pair(0) => (format!("(tl {})", x(0)), (*l).clone()),
            ("cons", [h, List(e)]) if *h == &**e => (format!("(cons {} {})", x(0), x(1)), xs[1].1.clone()),
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
                    if let Some((x, Sort::List(_))) = self.exp(*a, None, pairs) {
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
