//! Specifications in procedure types: `(subr E ((x int) …) Q (requires
//! p) (ensures r q))` (`docs/research/typed-cellular-code.md`, §8). The
//! checker reads them, sees that they speak of integers and booleans of
//! the procedure's own, and carries them in its type; within another
//! (behavioural subtyping) is the logic's (`crate::logic::spec_within`).
//! What a body or a call owes them, the cells' verifier proves
//! (`crate::typed_cells`).

use crate::ast::{Named, Rel, Spec, Ty, TyId};
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
        let Ty::Subr { conv, effect, params: ps, result, .. } = self.arena.get(t).clone() else { unreachable!("a subr just read") };
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
        let spec = Spec { params: pnames, result: rname, requires: requires.unwrap_or(Formula::True), ensures: ensures.unwrap_or(Formula::True) };
        Ok(self.arena.ty(Ty::Subr { conv, effect, params: ps, result, spec: Some(Rc::new(spec)) }))
    }

    pub(crate) fn is_int(&self, t: TyId) -> bool {
        let t = self.arena.resolve(t);
        t == self.int || matches!(self.arena.get(t), Ty::Nat(_))
    }

    pub(crate) fn is_bool(&self, t: TyId) -> bool {
        let t = self.arena.resolve(t);
        t == self.bool_ || matches!(self.arena.get(t), Ty::Proving { .. })
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
                    Some((_, named, t)) if self.is_bool(*t) => Ok(Formula::Holds(*named)),
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
            _ => Err(FxError::at(s.span, usage)),
        }
    }

    /// An integer: a literal, a name of an `int` or a `nat`, `(+ a …)`,
    /// `(- a)`, `(- a b …)`, `(* a …)`.
    fn spec_expr(&mut self, s: &Syntax, names: &Names) -> R<Expr<Named>> {
        let usage = "an integer: a literal, an `int` or `nat` named, `(+ a …)`, `(- a b …)` or `(* a …)`";
        match &s.datum {
            Datum::Number(fixpt_read::Num::Int(k)) => return Ok(Expr::Lit(*k)),
            Datum::Symbol(x) => {
                return match names.iter().find(|(n, ..)| n == x) {
                    Some((_, named, t)) if self.is_int(*t) => Ok(Expr::Atom(*named)),
                    Some(_) => Err(FxError::at(s.span, format!("`{}` is not an `int`", self.name(*x)))),
                    None => Err(FxError::at(s.span, format!("`{}` names no parameter or result here", self.name(*x)))),
                };
            }
            _ => {}
        }
        let items = s.as_proper_list().ok_or_else(|| FxError::at(s.span, usage))?.to_vec();
        let head = items.first().and_then(|h| h.as_symbol()).map(|h| self.name(h).to_string()).unwrap_or_default();
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
