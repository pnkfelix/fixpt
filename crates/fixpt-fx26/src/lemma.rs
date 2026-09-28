//! Lemmas: definitions whose declared type is a subtyping proposition,
//! `(proves (<= A B))`, whose body proves it (`docs/research/gadts.md`, N3).
//!
//! A proof is an ordinary function `A → B` (after a coercion for each
//! hypothesis) that takes apart what it was given and rebuilds the same
//! tags and labels, applying a hypothesis or another proof only to what was
//! given at the same place, and using itself only under a constructor it
//! has rebuilt: a guarded structural identity. So every `A` already is a
//! `B`; nothing need call the proof, and subtyping uses what it proves.

use std::collections::{HashMap, HashSet};

use crate::ast::{ArmBind, D, DVar, Exp, ExpId, Kind, Region, Ty, TyId};
use crate::check::Checker;
use crate::error::{FxError, R};
use fixpt_read::Sym;

/// A proposition proved: for every instance of `binders`, if each of `hyps`
/// holds then `lhs ≤ rhs`; and the definition that proves it.
#[derive(Clone, Debug)]
pub struct Lemma {
    pub binders: Vec<(DVar, Kind)>,
    pub lhs: TyId,
    pub rhs: TyId,
    pub hyps: Vec<(TyId, TyId)>,
    pub by: Option<(Sym, TyId)>,
}

/// A place in what a proof was given: a variable and the labels extracted.
#[derive(Clone, PartialEq, Debug)]
struct Pos {
    var: Sym,
    path: Vec<Sym>,
}

struct Proof {
    me: Sym,
    hyps: Vec<Sym>,
    want: String,
}

impl Checker {
    /// Whether `e`, the body of `name`, proves `l`; an error saying where
    /// it does not.
    pub(crate) fn check_proof(&mut self, l: &Lemma, name: Sym, e: ExpId) -> R<()> {
        let want = format!("`{} ≤ {}`", self.show_ty(l.lhs), self.show_ty(l.rhs));
        let mut x = e;
        while let Exp::PLambda { body, .. } | Exp::The { exp: body, .. } = self.arena.exp_at(x) {
            x = *body;
        }
        let Exp::Lambda { params, body } = self.arena.exp_at(x).clone() else {
            return Err(FxError::at(self.arena.span_of(e), format!("a proof of {want} is a lambda")));
        };
        let n = l.hyps.len();
        if params.len() != n + 1 {
            return Err(FxError::at(
                self.arena.span_of(x),
                format!("a proof of {want} takes a coercion for each hypothesis, then what it proves of"),
            ));
        }
        let p = Proof { me: name, hyps: params[..n].iter().map(|(s, _)| *s).collect(), want };
        let given = Pos { var: params[n].0, path: Vec::new() };
        self.rebuild(body, &given, l.lhs, false, &p)
    }

    fn not_proof(&self, e: ExpId, p: &Proof, why: &str) -> FxError {
        FxError::at(self.arena.span_of(e), format!("this does not prove {}: {why}", p.want))
    }

    /// `e` under ascriptions and generative types' conversions, which are
    /// the identity.
    fn strip_conversions(&self, mut e: ExpId) -> ExpId {
        loop {
            match self.arena.exp_at(e) {
                Exp::The { exp, .. } => e = *exp,
                Exp::App { fun, args } if args.len() == 1 && self.names_conversion(*fun) => e = args[0],
                _ => return e,
            }
        }
    }

    fn names_conversion(&self, f: ExpId) -> bool {
        let mut f = f;
        while let Exp::Proj { body, .. } | Exp::The { exp: body, .. } = self.arena.exp_at(f) {
            f = *body;
        }
        match self.arena.exp_at(f) {
            Exp::Var(s) => self.lookup(*s).is_some_and(|t| self.conversions.contains(&(*s, t))),
            _ => false,
        }
    }

    /// The place `e` names, if it names one: a variable, and extractions.
    fn place_of(&self, e: ExpId) -> Option<Pos> {
        match self.arena.exp_at(self.strip_conversions(e)).clone() {
            Exp::Var(s) => Some(Pos { var: s, path: Vec::new() }),
            Exp::Extract(x, l) => {
                let mut p = self.place_of(x)?;
                p.path.push(l);
                Some(p)
            }
            _ => None,
        }
    }

    /// What `e`'s operator names, under projections and ascriptions.
    fn operator(&self, mut f: ExpId) -> Option<Sym> {
        while let Exp::Proj { body, .. } | Exp::The { exp: body, .. } = self.arena.exp_at(f) {
            f = *body;
        }
        match self.arena.exp_at(f) {
            Exp::Var(s) => Some(*s),
            _ => None,
        }
    }

    /// `t` with generative types unfolded, as far as they go.
    fn unfold_all(&mut self, mut t: TyId) -> TyId {
        for _ in 0..64 {
            t = self.arena.resolve(t);
            match self.arena.get(t).clone() {
                Ty::Named { which, args } => t = self.unfold(which, &args),
                _ => return t,
            }
        }
        t
    }

    /// Whether `e` rebuilds, as the identity, what was given at `at`, of
    /// type `ty`; `guarded` once something has been rebuilt above it.
    fn rebuild(&mut self, e: ExpId, at: &Pos, ty: TyId, guarded: bool, p: &Proof) -> R<()> {
        let e = self.strip_conversions(e);
        if self.place_of(e).as_ref() == Some(at) {
            return Ok(());
        }
        match self.arena.exp_at(e).clone() {
            Exp::App { fun, args } => {
                let Some(f) = self.operator(fun) else {
                    return Err(self.not_proof(e, p, "a proof may call only its hypotheses, itself, or another proof"));
                };
                if p.hyps.contains(&f) {
                    return match &args[..] {
                        [a] if self.place_of(*a).as_ref() == Some(at) => Ok(()),
                        _ => Err(self.not_proof(e, p, "a hypothesis applies only to what was given here")),
                    };
                }
                let is_self = f == p.me;
                let is_lemma = self.lookup(f).is_some_and(|t| self.lemmas.iter().any(|l| l.by == Some((f, t))));
                if !is_self && !is_lemma {
                    return Err(self.not_proof(e, p, "a proof may call only its hypotheses, itself, or another proof"));
                }
                if is_self && !guarded {
                    return Err(self.not_proof(e, p, "it uses itself before rebuilding anything, which proves nothing"));
                }
                let Some((last, coercions)) = args.split_last() else {
                    return Err(self.not_proof(e, p, "a proof applies to something"));
                };
                if self.place_of(*last).as_ref() != Some(at) {
                    return Err(self.not_proof(*last, p, "a proof applies only to what was given here"));
                }
                for c in coercions {
                    self.proof_coercion(*c, guarded, p)?;
                }
                Ok(())
            }
            Exp::TagCase { scrutinee, arms, els } => {
                if self.place_of(scrutinee).as_ref() != Some(at) {
                    return Err(self.not_proof(scrutinee, p, "a proof takes apart only what was given here"));
                }
                let view = self.unfold_all(ty);
                let Ty::Sum(variants) = self.arena.get(view).clone() else {
                    return Err(self.not_proof(scrutinee, p, "what is given here is not a sum"));
                };
                for arm in &arms {
                    let names = arm.names();
                    if names.iter().any(|n| *n == at.var || *n == p.me || p.hyps.contains(n)) {
                        return Err(self.not_proof(arm.body, p, "a proof may not rebind the names it relies on"));
                    }
                    let Some(vt) = variants.iter().find(|(l, _)| *l == arm.tag).map(|(_, t)| *t) else {
                        return Err(self.not_proof(arm.body, p, "an arm for a tag that is not there"));
                    };
                    let body = self.strip_conversions(arm.body);
                    let Exp::Sum(tag, inner) = self.arena.exp_at(body).clone() else {
                        return Err(self.not_proof(arm.body, p, "each arm rebuilds its own tag"));
                    };
                    if tag != arm.tag {
                        return Err(self.not_proof(arm.body, p, "each arm rebuilds its own tag"));
                    }
                    match &arm.bind {
                        ArmBind::Value(v) => self.rebuild(inner, &Pos { var: *v, path: Vec::new() }, vt, true, p)?,
                        ArmBind::Fields(xs) => {
                            let vview = self.unfold_all(vt);
                            let Ty::Product(fs) = self.arena.get(vview).clone() else {
                                return Err(self.not_proof(arm.body, p, "fields of something that is not a product"));
                            };
                            let inner = self.strip_conversions(inner);
                            let Exp::Product(gs) = self.arena.exp_at(inner).clone() else {
                                return Err(self.not_proof(inner, p, "each arm rebuilds its fields"));
                            };
                            if gs.len() != fs.len() || xs.len() != fs.len() || gs.iter().zip(&fs).any(|((g, _), (f, _))| g != f) {
                                return Err(self.not_proof(inner, p, "each arm rebuilds its fields, in order"));
                            }
                            for ((x, (_, ft)), (_, g)) in xs.iter().zip(&fs).zip(&gs) {
                                self.rebuild(*g, &Pos { var: *x, path: Vec::new() }, *ft, true, p)?;
                            }
                        }
                    }
                }
                if let Some((y, body)) = els {
                    if y == p.me || p.hyps.contains(&y) {
                        return Err(self.not_proof(body, p, "a proof may not rebind the names it relies on"));
                    }
                    self.rebuild(body, &Pos { var: y, path: Vec::new() }, ty, guarded, p)?;
                }
                Ok(())
            }
            Exp::Product(gs) => {
                let view = self.unfold_all(ty);
                let Ty::Product(fs) = self.arena.get(view).clone() else {
                    return Err(self.not_proof(e, p, "what is given here is not a product"));
                };
                if gs.len() != fs.len() || gs.iter().zip(&fs).any(|((g, _), (f, _))| g != f) {
                    return Err(self.not_proof(e, p, "a product is rebuilt with its fields, in order"));
                }
                for ((l, g), (_, ft)) in gs.iter().zip(&fs) {
                    let mut path = at.path.clone();
                    path.push(*l);
                    self.rebuild(*g, &Pos { var: at.var, path }, *ft, true, p)?;
                }
                Ok(())
            }
            _ => Err(self.not_proof(e, p, "a proof may only take apart and rebuild what it was given")),
        }
    }

    /// A coercion a proof passes to a proof: a hypothesis, a proof, itself
    /// (under a constructor), or a lambda whose parameter is annotated and
    /// whose body rebuilds it.
    fn proof_coercion(&mut self, c: ExpId, guarded: bool, p: &Proof) -> R<()> {
        let c = self.strip_conversions(c);
        match self.arena.exp_at(c).clone() {
            Exp::Var(s) if p.hyps.contains(&s) => Ok(()),
            Exp::Var(s) if s == p.me => {
                if guarded {
                    Ok(())
                } else {
                    Err(self.not_proof(c, p, "it passes itself on before rebuilding anything"))
                }
            }
            Exp::Var(s) if self.lookup(s).is_some_and(|t| self.lemmas.iter().any(|l| l.by == Some((s, t)))) => Ok(()),
            Exp::Lambda { params, body } => match &params[..] {
                [(x, Some(t))] => {
                    if *x == p.me || p.hyps.contains(x) {
                        return Err(self.not_proof(c, p, "a proof may not rebind the names it relies on"));
                    }
                    self.rebuild(body, &Pos { var: *x, path: Vec::new() }, *t, guarded, p)
                }
                _ => Err(self.not_proof(c, p, "a coercion given to a proof takes one parameter, with its type written")),
            },
            _ => Err(self.not_proof(c, p, "a proof is given only hypotheses, proofs, or coercions that rebuild")),
        }
    }

    // ------------------------------------------------------ using lemmas

    /// Whether some lemma could relate `a` to `b`, by their outermost shapes.
    pub(crate) fn lemma_may_apply(&self, a: TyId, b: TyId) -> bool {
        let head = |c: &Checker, l: &Lemma, pat: TyId, t: TyId| {
            let (pt, tt) = (c.arena.get(c.arena.resolve(pat)), c.arena.get(t));
            match (pt, tt) {
                (Ty::Var(v), _) if l.binders.iter().any(|(x, _)| x == v) => true,
                (Ty::Named { which: g, .. }, Ty::Named { which: h, .. }) => g == h,
                _ => std::mem::discriminant(pt) == std::mem::discriminant(tt),
            }
        };
        self.lemmas.iter().any(|l| head(self, l, l.lhs, a) && head(self, l, l.rhs, b))
    }

    /// Whether some lemma, instantiated to fit `a` and `b`, has hypotheses
    /// that hold, each checked by `holds`.
    pub(crate) fn lemma_instances(&mut self, a: TyId, b: TyId) -> Vec<Vec<(TyId, TyId)>> {
        let mut out = Vec::new();
        for l in self.lemmas.clone() {
            let mut map = HashMap::new();
            let mut seen = HashSet::new();
            if !(self.match_ty(&l, l.lhs, a, &mut map, &mut seen) && self.match_ty(&l, l.rhs, b, &mut map, &mut seen)) {
                continue;
            }
            if l.binders.iter().any(|(v, _)| !map.contains_key(v)) {
                continue;
            }
            let hyps = l.hyps.iter().map(|(x, y)| (self.subst(*x, &map), self.subst(*y, &map))).collect();
            out.push(hyps);
        }
        out
    }

    /// Whether `t` is `pat` with its binders standing for something,
    /// recorded in `map`.
    fn match_ty(&mut self, l: &Lemma, pat: TyId, t: TyId, map: &mut HashMap<DVar, D>, seen: &mut HashSet<(TyId, TyId)>) -> bool {
        let (pat, t) = (self.arena.resolve(pat), self.arena.resolve(t));
        if !seen.insert((pat, t)) {
            return true;
        }
        let bound = |v: &DVar| l.binders.iter().any(|(x, _)| x == v);
        match (self.arena.get(pat).clone(), self.arena.get(t).clone()) {
            (Ty::Var(v), _) if bound(&v) => match map.get(&v).cloned() {
                Some(D::Type(u)) => self.subtype(u, t) && self.subtype(t, u),
                Some(_) => false,
                None => {
                    map.insert(v, D::Type(t));
                    true
                }
            },
            (Ty::Named { which: g, args: xs }, Ty::Named { which: h, args: ys }) => {
                g == h && xs.iter().zip(&ys).all(|(x, y)| self.match_d(l, x, y, map, seen))
            }
            (Ty::Pair(a1, b1, r1), Ty::Pair(a2, b2, r2)) => {
                self.match_region(l, r1, r2, map) && self.match_ty(l, a1, a2, map, seen) && self.match_ty(l, b1, b2, map, seen)
            }
            (Ty::Ref(x, r), Ty::Ref(y, s)) | (Ty::Array(x, r), Ty::Array(y, s)) | (Ty::ICell(x, r), Ty::ICell(y, s)) => {
                self.match_region(l, r, s, map) && self.match_ty(l, x, y, map, seen)
            }
            (Ty::Product(ps), Ty::Product(qs)) | (Ty::Sum(ps), Ty::Sum(qs)) => {
                ps.len() == qs.len()
                    && ps.iter().zip(&qs).all(|((a, x), (b, y))| a == b && self.match_ty(l, *x, *y, map, seen))
            }
            (Ty::Subr { conv: c1, effect: e1, params: p1, result: r1 }, Ty::Subr { conv: c2, effect: e2, params: p2, result: r2 }) => {
                c1 == c2
                    && e1 == e2
                    && p1.len() == p2.len()
                    && p1.iter().zip(&p2).all(|(x, y)| self.match_ty(l, *x, *y, map, seen))
                    && self.match_ty(l, r1, r2, map, seen)
            }
            _ => self.subtype(pat, t) && self.subtype(t, pat),
        }
    }

    fn match_d(&mut self, l: &Lemma, x: &D, y: &D, map: &mut HashMap<DVar, D>, seen: &mut HashSet<(TyId, TyId)>) -> bool {
        match (x, y) {
            (D::Type(a), D::Type(b)) => self.match_ty(l, *a, *b, map, seen),
            (D::Region(r), D::Region(s)) => self.match_region(l, *r, *s, map),
            (D::Size(a), D::Size(b)) => a == b,
            (D::Conv(a), D::Conv(b)) => a == b,
            (D::Effect(d), D::Effect(e)) => {
                let var = d.0.iter().next().and_then(|a| match a {
                    crate::ast::Atom::Var(v) if d.0.len() == 1 && l.binders.iter().any(|(x, _)| x == v) => Some(*v),
                    _ => None,
                });
                match var {
                    Some(v) => match map.get(&v) {
                        Some(D::Effect(f)) => f == e,
                        Some(_) => false,
                        None => {
                            map.insert(v, D::Effect(e.clone()));
                            true
                        }
                    },
                    None => d == e,
                }
            }
            _ => false,
        }
    }

    fn match_region(&self, l: &Lemma, r: Region, s: Region, map: &mut HashMap<DVar, D>) -> bool {
        match r {
            Region::Var(v) if l.binders.iter().any(|(x, _)| *x == v) => match map.get(&v) {
                Some(D::Region(q)) => *q == s,
                Some(_) => false,
                None => {
                    map.insert(v, D::Region(s));
                    true
                }
            },
            _ => r == s,
        }
    }
}
