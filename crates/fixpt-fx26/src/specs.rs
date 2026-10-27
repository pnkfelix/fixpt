//! Specifications in procedure types: `(subr E ((x : int) …) Q (requires
//! p) (ensures r q))` (`docs/research/typed-cellular-code.md`, §8). The
//! checker reads them, sees that they speak of integers and booleans of
//! the procedure's own, and carries them in its type; within another
//! (behavioural subtyping) is the logic's (`crate::logic::spec_within`).
//! What a body or a call owes them, the cells' verifier proves
//! (`crate::typed_cells`).

use crate::ast::{Named, Prop, Rel, Spec, Term, Ty, TyId};
use crate::check::Checker;
use crate::error::{FxError, R};
use crate::logic::{Expr, Formula};
use fixpt_read::{Datum, Sym, Syntax};
use std::rc::Rc;

/// Whether `s` is a specification's clause: `(requires …)` or `(ensures
/// …)`.
pub(crate) fn clause(c: &Checker, s: &Syntax) -> bool {
    s.as_proper_list().and_then(|l| l.first()).and_then(|h| h.as_symbol()).is_some_and(|h| matches!(c.name(h), "requires" | "ensures"))
}

/// What a proposition may name: each name, what it names, and its type.
type Names = Vec<(Sym, Named, TyId)>;

impl Checker {
    /// The specification of `t`, a `subr`, if it has one.
    pub(crate) fn spec_of(&self, t: TyId) -> Option<Rc<Spec>> {
        match self.arena.get(self.arena.resolve(t)) {
            Ty::Subr { spec, .. } => spec.clone(),
            _ => None,
        }
    }

    /// Why procedure type `got` is not within `want`, if its specification
    /// is why: a line saying so, or nothing.
    pub(crate) fn spec_delta(&self, got: TyId, want: TyId) -> &'static str {
        let (g, w) = (self.spec_of(got), self.spec_of(want));
        if (g.is_some() || w.is_some()) && !crate::logic::spec_within(g.as_deref(), w.as_deref()) {
            "\n  it requires more, or ensures less, than is expected, as far as the prover can tell"
        } else {
            ""
        }
    }

    /// `t`, a `subr` type just read from `params` (its parameters as
    /// written) and `clauses`, with the specification they say.
    pub(crate) fn specified(&mut self, t: TyId, params: &Syntax, clauses: &[Syntax]) -> R<TyId> {
        let Ty::Subr { conv, effect, params: ps, result, spec: latent } = self.arena.get(t).clone() else { unreachable!("a subr just read") };
        let written: Vec<Syntax> = match &params.datum {
            Datum::Nil => Vec::new(),
            _ => params.as_proper_list().map(|l| l.to_vec()).unwrap_or_default(),
        };
        let pnames: Vec<Option<Sym>> = written.iter().map(|p| self.named_param(p).map(|(n, _)| n)).collect();
        let names: Names = pnames.iter().zip(&ps).enumerate().filter_map(|(i, (n, t))| Some(((*n)?, Named::Param(i), *t))).collect();
        let (mut requires, mut ensures, mut rname) = (None, None, None);
        for c in clauses {
            let items = c.as_proper_list().expect("a clause");
            let head = self.name(items[0].as_symbol().expect("a clause")).to_string();
            match (head.as_str(), &items[1..]) {
                ("requires", [p]) if requires.is_none() && ensures.is_none() => requires = Some(self.spec_prop(p, &names)?),
                ("ensures", [r, q]) if ensures.is_none() => {
                    let Some(r) = r.as_symbol() else {
                        return Err(FxError::at(r.span, "the result's name: `(ensures name proposition)`"));
                    };
                    let mut with_result = names.clone();
                    with_result.push((r, Named::Result, result));
                    ensures = Some(self.spec_prop(q, &with_result)?);
                    rname = Some(r);
                }
                _ => return Err(FxError::at(c.span, "a specification is `(requires proposition)`, then `(ensures name proposition)`, each at most once")),
            }
        }
        // What a `(bool …)` result proves, first.
        let ensures = match (latent, ensures) {
            (Some(l), Some(e)) => Formula::And(vec![l.ensures.clone(), e]),
            (Some(l), None) => l.ensures.clone(),
            (None, e) => e.unwrap_or(Formula::True),
        };
        let spec = Spec { params: pnames, result: rname, requires: requires.unwrap_or(Formula::True), ensures };
        Ok(self.arena.ty(Ty::Subr { conv, effect, params: ps, result, spec: Some(Rc::new(spec)) }))
    }

    pub(crate) fn is_int(&self, t: TyId) -> bool {
        let t = self.arena.resolve(t);
        t == self.int || matches!(self.arena.get(t), Ty::Nat(_))
    }

    pub(crate) fn is_bool(&self, t: TyId) -> bool {
        let t = self.arena.resolve(t);
        t == self.bool_
    }

    /// A proposition: `(< a b)`, `(<= a b)`, `(= a b)`, `(> a b)`, `(>=
    /// a b)` of integers; `(not p)`, `(and p …)`, `(or p …)`, `(implies p
    /// q)`; `#t`, `#f`; or a name of a `bool`.
    fn spec_prop(&mut self, s: &Syntax, names: &Names) -> R<Formula<Named>> {
        let usage = "a proposition: `(< a b)`, `(<= a b)`, `(= a b)`, `(> a b)`, `(>= a b)`, `(not p)`, `(and p …)`, `(or p …)`, `(implies p q)`, `#t`, `#f`, or a `bool` named";
        match &s.datum {
            Datum::Bool(true) => return Ok(Formula::True),
            Datum::Bool(false) => return Ok(Formula::False),
            Datum::Symbol(x) => {
                return match names.iter().find(|(n, ..)| n == x) {
                    Some((_, named, t)) if self.is_bool(*t) => Ok(Formula::Holds(named.clone())),
                    Some(_) => Err(FxError::at(s.span, format!("`{}` is not a `bool`, so not a proposition", self.name(*x)))),
                    None => Err(FxError::at(s.span, format!("`{}` names no parameter or result here", self.name(*x)))),
                };
            }
            _ => {}
        }
        let items = s.as_proper_list().ok_or_else(|| FxError::at(s.span, usage))?.to_vec();
        let head = items.first().and_then(|h| h.as_symbol()).map(|h| self.name(h).to_string()).unwrap_or_default();
        let args = items.get(1..).unwrap_or_default();
        let rel = |c: &mut Self, r: Rel, swap: bool| -> R<Formula<Named>> {
            let [x, y] = args else { return Err(FxError::at(s.span, format!("`({head} a b)`"))) };
            let (x, y) = (c.spec_expr(x, names)?, c.spec_expr(y, names)?);
            Ok(if swap { Formula::Rel(r, y, x) } else { Formula::Rel(r, x, y) })
        };
        match head.as_str() {
            "<" => rel(self, Rel::Lt, false),
            "<=" => rel(self, Rel::Le, false),
            "=" => rel(self, Rel::Eq, false),
            ">" => rel(self, Rel::Lt, true),
            ">=" => rel(self, Rel::Le, true),
            "not" => match args {
                [p] => Ok(Formula::Not(Box::new(self.spec_prop(p, names)?))),
                _ => Err(FxError::at(s.span, "`(not p)`")),
            },
            "and" | "or" => {
                let ps = args.iter().map(|p| self.spec_prop(p, names)).collect::<R<Vec<_>>>()?;
                Ok(if head == "and" { Formula::And(ps) } else { Formula::Or(ps) })
            }
            "implies" => match args {
                [p, q] => Ok(Formula::Implies(Box::new(self.spec_prop(p, names)?), Box::new(self.spec_prop(q, names)?))),
                _ => Err(FxError::at(s.span, "`(implies p q)`")),
            },
            _ if self.spec_callee(&items).is_some() => Ok(Formula::Holds(self.spec_call(s, &items, names, true)?)),
            _ => Err(FxError::at(s.span, usage)),
        }
    }

    /// Of `(f a …)`, `f`, if its innermost binding is a global's (a
    /// top-level definition's).
    fn spec_callee(&self, items: &[Syntax]) -> Option<Sym> {
        let f = items.first()?.as_symbol()?;
        self.env.rpos(f).is_some_and(|i| self.global_slots.contains(&i)).then_some(f)
    }

    /// `(f a …)`, a logic function's value at its arguments
    /// (`docs/research/specs-and-counterexamples.md`, §5): `f` a global
    /// procedure, `pure` (so ending, and of nothing but its arguments), of
    /// a `bool` result (`bool`) or an `int`'s or `nat`'s; each argument an
    /// integer, where `f` takes one, or else a parameter or the result,
    /// named. (Whether that is of the type `f` takes is not asked here, as
    /// the checker written in FX-26 reads specifications before it has
    /// subtyping: a call is a function of the logic's whatever it is
    /// given, and a run checking it says.)
    fn spec_call(&mut self, s: &Syntax, items: &[Syntax], names: &Names, bool: bool) -> R<Named> {
        let f = self.spec_callee(items).expect("a global");
        let fname = self.name(f).to_string();
        let t = self.env[self.env.rpos(f).expect("bound")].1;
        let Ty::Subr { effect, params, result, .. } = self.arena.get(self.arena.resolve(t)).clone() else {
            return Err(FxError::at(s.span, format!("`{fname}` is called in a specification, and is no procedure")));
        };
        if !effect.is_pure() {
            return Err(FxError::at(s.span, format!("`{fname}` is called in a specification, so must be `pure`")));
        }
        if bool && !self.is_bool(result) {
            return Err(FxError::at(s.span, format!("`{fname}` gives no `bool`, so is no proposition")));
        }
        if !bool && !self.is_int(result) {
            return Err(FxError::at(s.span, format!("`{fname}` gives no `int` or `nat`, so is no integer")));
        }
        let args = &items[1..];
        if args.len() != params.len() {
            return Err(FxError::at(s.span, format!("`{fname}` takes {} arguments, not {}", params.len(), args.len())));
        }
        let mut xs = Vec::new();
        for (a, p) in args.iter().zip(&params) {
            if self.is_int(*p) {
                xs.push(self.spec_expr(a, names)?);
                continue;
            }
            let found = a.as_symbol().and_then(|x| names.iter().find(|(n, ..)| *n == x));
            let Some((_, named, _)) = found.cloned() else {
                return Err(FxError::at(a.span, format!("an argument of `{fname}` in a specification: a parameter or the result, named")));
            };
            xs.push(Expr::Atom(named));
        }
        Ok(Named::Call(f, Rc::new(xs)))
    }

    /// An integer: a literal, a name of an `int` or a `nat`, `(+ a …)`,
    /// `(- a)`, `(- a b …)`, `(* a …)`.
    fn spec_expr(&mut self, s: &Syntax, names: &Names) -> R<Expr<Named>> {
        let usage = "an integer: a literal, an `int` or `nat` named, `(+ a …)`, `(- a b …)` or `(* a …)`";
        match &s.datum {
            Datum::Number(fixpt_read::Num::Int(k)) => return Ok(Expr::Lit(*k)),
            Datum::Symbol(x) => {
                return match names.iter().find(|(n, ..)| n == x) {
                    Some((_, named, t)) if self.is_int(*t) => Ok(Expr::Atom(named.clone())),
                    Some(_) => Err(FxError::at(s.span, format!("`{}` is not an `int`", self.name(*x)))),
                    None => Err(FxError::at(s.span, format!("`{}` names no parameter or result here", self.name(*x)))),
                };
            }
            _ => {}
        }
        let items = s.as_proper_list().ok_or_else(|| FxError::at(s.span, usage))?.to_vec();
        let head = items.first().and_then(|h| h.as_symbol()).map(|h| self.name(h).to_string()).unwrap_or_default();
        if !matches!(head.as_str(), "+" | "-" | "*") && self.spec_callee(&items).is_some() {
            return Ok(Expr::Atom(self.spec_call(s, &items, names, false)?));
        }
        let args = items.get(1..).unwrap_or_default().iter().map(|a| self.spec_expr(a, names)).collect::<R<Vec<_>>>()?;
        let fold = |args: Vec<Expr<Named>>, f: fn(Box<Expr<Named>>, Box<Expr<Named>>) -> Expr<Named>| {
            let mut it = args.into_iter();
            let first = it.next().expect("one at least");
            it.fold(first, |a, b| f(Box::new(a), Box::new(b)))
        };
        match (head.as_str(), args.len()) {
            ("+", 1..) => Ok(fold(args, Expr::Add)),
            ("*", 1..) => Ok(fold(args, Expr::Mul)),
            ("-", 1) => Ok(Expr::Sub(Box::new(Expr::Lit(0)), Box::new(args.into_iter().next().expect("one")))),
            ("-", 2..) => Ok(fold(args, Expr::Sub)),
            _ => Err(FxError::at(s.span, usage)),
        }
    }
}

/// What a test proves, `(bool (then P …) (else Q …))`, as an `ensures` of
/// its result: `(and (implies r (and P …)) (implies (not r) (and Q …)))`.
pub(crate) fn latent(then: &[Prop], els: &[Prop]) -> Formula<Named> {
    let all = |ps: &[Prop]| Formula::And(ps.iter().map(prop_formula).collect());
    let r = Formula::Holds(Named::Result);
    Formula::And(vec![Formula::Implies(Box::new(r.clone()), Box::new(all(then))), Formula::Implies(Box::new(Formula::Not(Box::new(r))), Box::new(all(els)))])
}

/// An `ensures` as `latent` writes one, alone or the first of two
/// conjuncts: what it proves where true and where false, and the rest,
/// `true` if none.
pub(crate) fn latent_split(f: &Formula<Named>) -> Option<(Vec<Prop>, Vec<Prop>, Formula<Named>)> {
    let (l, rest) = match f {
        Formula::And(ps) if ps.len() == 2 && matches!(&ps[0], Formula::And(_)) => (&ps[0], ps[1].clone()),
        _ => (f, Formula::True),
    };
    let Formula::And(sides) = l else { return None };
    let [Formula::Implies(r, then), Formula::Implies(nr, els)] = &sides[..] else { return None };
    let props = |f: &Formula<Named>| match f {
        Formula::And(ps) => ps.iter().map(formula_prop).collect::<Option<Vec<Prop>>>(),
        _ => None,
    };
    let is_r = |f: &Formula<Named>| *f == Formula::Holds(Named::Result);
    if !is_r(r) || !matches!(&**nr, Formula::Not(x) if is_r(x)) {
        return None;
    }
    Some((props(then)?, props(els)?, rest))
}

/// What an `ensures` proves of the arguments where its result is true
/// (`yes`) or false: the propositions of each conjunct `(implies r p)`
/// (`(implies (not r) p)`), as a test's narrowing takes them (the call
/// rule's `ensures`, at a branch on the result).
pub(crate) fn latent_facts(f: &Formula<Named>, yes: bool) -> Vec<Prop> {
    fn conjuncts(f: &Formula<Named>, out: &mut Vec<Prop>) {
        match f {
            Formula::And(ps) => ps.iter().for_each(|p| conjuncts(p, out)),
            f => out.extend(formula_prop(f)),
        }
    }
    let mut out = Vec::new();
    match f {
        Formula::And(ps) => ps.iter().for_each(|p| out.extend(latent_facts(p, yes))),
        Formula::Implies(r, q) if yes && **r == Formula::Holds(Named::Result) => conjuncts(q, &mut out),
        Formula::Implies(r, q) if !yes && matches!(&**r, Formula::Not(x) if **x == Formula::Holds(Named::Result)) => conjuncts(q, &mut out),
        _ => {}
    }
    out
}

fn prop_formula(p: &Prop) -> Formula<Named> {
    let term = |t: &Term| match t {
        Term::Param(i) => Expr::Atom(Named::Param(*i)),
        Term::Length(i) => Expr::Atom(Named::Length(*i)),
        Term::Lit(k) => Expr::Lit(*k),
    };
    match p {
        Prop::Shape { param, shape, negated: false } => Formula::Holds(Named::Shape(*param, *shape)),
        Prop::Shape { param, shape, negated: true } => Formula::Not(Box::new(Formula::Holds(Named::Shape(*param, *shape)))),
        Prop::Acyclic(i) => Formula::Holds(Named::Acyclic(*i)),
        Prop::Nat(i) => Formula::Holds(Named::Nat(*i)),
        Prop::Length(i, j) => Formula::Holds(Named::LengthIs(*i, *j)),
        Prop::Rel { op, a, b } => Formula::Rel(*op, term(a), term(b)),
    }
}

/// A proposition `prop_formula` makes, as the `Prop` it is; `(not (= a
/// b))` too.
fn formula_prop(f: &Formula<Named>) -> Option<Prop> {
    let term = |e: &Expr<Named>| match e {
        Expr::Atom(Named::Param(i)) => Some(Term::Param(*i)),
        Expr::Atom(Named::Length(i)) => Some(Term::Length(*i)),
        Expr::Lit(k) => Some(Term::Lit(*k)),
        _ => None,
    };
    Some(match f {
        Formula::Holds(Named::Shape(param, shape)) => Prop::Shape { param: *param, shape: *shape, negated: false },
        Formula::Not(x) => match &**x {
            Formula::Holds(Named::Shape(param, shape)) => Prop::Shape { param: *param, shape: *shape, negated: true },
            Formula::Rel(Rel::Eq, a, b) => Prop::Rel { op: Rel::Ne, a: term(a)?, b: term(b)? },
            _ => return None,
        },
        Formula::Holds(Named::Acyclic(i)) => Prop::Acyclic(*i),
        Formula::Holds(Named::Nat(i)) => Prop::Nat(*i),
        Formula::Holds(Named::LengthIs(i, j)) => Prop::Length(*i, *j),
        Formula::Rel(op, a, b) => Prop::Rel { op: *op, a: term(a)?, b: term(b)? },
        _ => return None,
    })
}
