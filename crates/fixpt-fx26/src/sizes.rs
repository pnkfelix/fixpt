//! Sizes: linear expressions over size variables, and what the facts in
//! scope show about them (`docs/research/sizes.md`, N5b).
//!
//! A fact is `lin = 0` or `lin ≥ 0`, learned in a branch: `(null? xs)` with
//! `xs : (nlist T n)` gives `n = 0` in the `then` and `n - 1 ≥ 0` in the
//! `else`. An equality is used to rewrite a variable away; an inequality is
//! used as it is, or with a constant to spare; and when neither shows what
//! is asked, the inequalities together, by Fourier–Motzkin elimination
//! (N5c).

use std::collections::{BTreeMap, HashSet};

use crate::ast::{D, DVar, Exp, ExpId, Kind, Size, Ty, TyId};
use fixpt_read::Sym;
use crate::check::Checker;

/// Where in a type an occurrence is: given back (`Pos`), supplied by a
/// caller (`Neg`), or both, as in anything that can be written (`Inv`).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum Polarity {
    Pos,
    Neg,
    Inv,
}

impl Polarity {
    fn flip(self) -> Polarity {
        match self {
            Polarity::Pos => Polarity::Neg,
            Polarity::Neg => Polarity::Pos,
            Polarity::Inv => Polarity::Inv,
        }
    }
}

/// A fact: `lin = 0` (`eq`) or `lin ≥ 0`.
#[derive(Clone, Debug)]
pub struct SizeFact {
    pub lin: Size,
    pub eq: bool,
}

/// A linear size as a constant and coefficients by variable.
fn parts(s: &Size) -> Option<(i64, BTreeMap<DVar, i64>)> {
    match s {
        Size::Finite => None,
        Size::Lin { k, terms } => Some((*k, terms.iter().copied().collect())),
    }
}

fn from_parts(k: i64, terms: BTreeMap<DVar, i64>) -> Size {
    Size::Lin { k, terms: terms.into_iter().filter(|(_, c)| *c != 0).collect() }
}

impl Size {
    /// A size variable.
    pub fn var(v: DVar) -> Size {
        Size::Lin { k: 0, terms: vec![(v, 1)] }
    }

    /// `self + c·other`; `finite` if either is.
    pub fn add_scaled(&self, other: &Size, c: i64) -> Size {
        match (parts(self), parts(other)) {
            (Some((k, mut t)), Some((k2, t2))) => {
                for (v, c2) in t2 {
                    *t.entry(v).or_insert(0) += c * c2;
                }
                from_parts(k + c * k2, t)
            }
            _ => Size::Finite,
        }
    }

    /// `self` with `v` replaced by `by`.
    pub fn replace(&self, v: DVar, by: &Size) -> Size {
        match parts(self) {
            Some((k, mut t)) => match t.remove(&v) {
                Some(c) => from_parts(k, t).add_scaled(by, c),
                None => self.clone(),
            },
            None => Size::Finite,
        }
    }
}

/// How many constraints Fourier–Motzkin elimination may have at once
/// before it gives up (`Checker::refuted_below`).
const FM_LIMIT: usize = 64;

/// `c ≥ 0` as integers allow: its coefficients divided by their gcd, and
/// its constant rounded down after the same division.
fn tightened(c: &Size) -> Size {
    let Some((k, t)) = parts(c) else { return c.clone() };
    let g = t.values().fold(0i64, |g, c| gcd(g, c.abs()));
    if g <= 1 {
        return c.clone();
    }
    from_parts(k.div_euclid(g), t.into_iter().map(|(v, c)| (v, c / g)).collect())
}

fn gcd(a: i64, b: i64) -> i64 {
    if b == 0 { a } else { gcd(b, a % b) }
}

/// `s` with `map`'s sizes for its variables.
pub(crate) fn subst_size(s: &Size, map: &std::collections::HashMap<DVar, D>) -> Size {
    let Some((_, t)) = parts(s) else { return Size::Finite };
    let mut out = s.clone();
    for v in t.keys() {
        if let Some(D::Size(by)) = map.get(v) {
            out = out.replace(*v, by);
        }
    }
    out
}

impl Checker {
    /// `s` with each variable an equality in scope determines rewritten
    /// away.
    fn reduced(&self, s: &Size) -> Size {
        let mut s = s.clone();
        for f in self.size_facts.iter().filter(|f| f.eq) {
            let Some((_, t)) = parts(&f.lin) else { continue };
            // A variable with coefficient ±1 in `lin = 0` is `-(rest)/c`.
            let Some((v, c)) = t.iter().find(|(_, c)| c.abs() == 1).map(|(v, c)| (*v, *c)) else { continue };
            let rest = f.lin.add_scaled(&Size::var(v), -c);
            let by = Size::lit(0).add_scaled(&rest, -c);
            s = s.replace(v, &by);
        }
        s
    }

    /// Whether the facts show `a = b`.
    pub(crate) fn size_eq(&self, a: &Size, b: &Size) -> bool {
        match (a, b) {
            (Size::Finite, Size::Finite) => true,
            (Size::Finite, _) | (_, Size::Finite) => false,
            _ => self.reduced(&a.add_scaled(b, -1)) == Size::lit(0),
        }
    }

    /// Whether the facts show `a ≥ 0`. Every size is a natural, so a sum
    /// of variables with coefficients and a constant, none negative, is;
    /// so is one that a fact `f ≥ 0` leaves so, as `a - f`.
    pub(crate) fn size_nonneg(&self, a: &Size) -> bool {
        let plainly = |s: &Size| match s {
            Size::Lin { k, terms } => *k >= 0 && terms.iter().all(|(_, c)| *c >= 0),
            Size::Finite => false,
        };
        let a = self.reduced(a);
        plainly(&a) || self.size_facts.iter().filter(|f| !f.eq).any(|f| plainly(&a.add_scaled(&self.reduced(&f.lin), -1))) || self.refuted_below(&a)
    }

    /// Whether the inequalities in scope, with every size a natural, leave
    /// no room for `a ≤ -1`: Fourier–Motzkin elimination (as Xi and
    /// Pfenning's Dependent ML decides its index constraints, from memory).
    /// Each variable in turn, lowest first, is eliminated by adding every
    /// constraint with it positive to every one with it negative, scaled
    /// so that it cancels; each sum is tightened as integers allow (divided
    /// by its coefficients' gcd, its constant rounded down). No room left
    /// shows as a constant constraint below 0. Sound, as rationals are more
    /// room than integers; incomplete, and it gives up past
    /// `FM_LIMIT` constraints. The FX-26 checker's is this, step
    /// for step.
    fn refuted_below(&self, a: &Size) -> bool {
        let Some(_) = parts(a) else { return false };
        let mut cs: Vec<Size> = self.size_facts.iter().filter(|f| !f.eq).map(|f| self.reduced(&f.lin)).filter(|c| parts(c).is_some()).collect();
        cs.push(Size::lit(-1).add_scaled(a, -1));
        let mut vars: Vec<DVar> = cs.iter().flat_map(|c| parts(c).map(|(_, t)| t.into_keys().collect::<Vec<_>>()).unwrap_or_default()).collect();
        vars.sort();
        vars.dedup();
        cs.extend(vars.iter().map(|v| Size::var(*v)));
        let coef = |c: &Size, v: DVar| parts(c).and_then(|(_, t)| t.get(&v).copied()).unwrap_or(0);
        for v in vars {
            let (mut next, mut pos, mut neg) = (Vec::new(), Vec::new(), Vec::new());
            for c in cs {
                match coef(&c, v) {
                    0 => next.push(c),
                    k if k > 0 => pos.push(c),
                    _ => neg.push(c),
                }
            }
            for p in &pos {
                for n in &neg {
                    let (x, y) = (coef(p, v), -coef(n, v));
                    next.push(tightened(&Size::lit(0).add_scaled(p, y).add_scaled(n, x)));
                }
            }
            if next.len() > FM_LIMIT {
                return false;
            }
            cs = next;
        }
        cs.iter().any(|c| matches!(c, Size::Lin { k, terms } if terms.is_empty() && *k < 0))
    }

    /// The size of the tail of a list of size `n`: one less, where the
    /// facts show `n ≥ 1`; `finite` otherwise.
    pub(crate) fn tail_size(&self, n: &Size) -> Size {
        match n {
            Size::Finite => Size::Finite,
            _ if self.size_nonneg(&n.plus(-1)) => n.plus(-1),
            _ => Size::Finite,
        }
    }

    /// Whether a list of size `m` is one of size `n`: the facts show them
    /// equal, or `n` is `finite`.
    pub(crate) fn size_le(&self, m: &Size, n: &Size) -> bool {
        matches!(n, Size::Finite) || self.size_eq(m, n)
    }

    /// The size an argument is, when it is a natural literal or a variable
    /// of type `(nat s)`.
    pub(crate) fn nat_size(&self, e: ExpId) -> Option<Size> {
        match self.arena.exp_at(e) {
            Exp::Int(k) if *k >= 0 => Some(Size::lit(*k)),
            Exp::Var(v) => match self.arena.get(self.arena.resolve(self.lookup(*v)?)) {
                Ty::Nat(s) => Some(s.clone()),
                _ => None,
            },
            _ => None,
        }
    }

    /// Whether `e` may be a natural of a size without being told what it
    /// is: a literal, a variable, or a `+`, `-`, `length`, `string-length`
    /// or `array-length`.
    pub(crate) fn natural_by_itself(&self, e: ExpId) -> bool {
        match self.arena.exp_at(e) {
            Exp::Int(_) | Exp::Var(_) => true,
            Exp::App { fun, .. } => self
                .standard_ref(*fun)
                .is_some_and(|op| matches!(self.interner.name(op), "+" | "-" | "length" | "string-length" | "array-length")),
            _ => false,
        }
    }

    /// What `test` shows about sizes when it holds, and when not.
    /// `(null? xs)`, `xs : (nlist T n)`: `n = 0`, or `n - 1 ≥ 0`. A
    /// comparison of naturals: `(< a b)`, `b - a - 1 ≥ 0`, or `a - b ≥ 0`;
    /// `(= a 0)`, `a = 0`, or, a natural not 0, `a - 1 ≥ 0`.
    ///
    /// An `or`, `(if a #t b)`, shows when it does not hold what `a` and `b`
    /// both show so; an `and`, `(if a b #f)`, when it holds what both show
    /// then; `(not x)` what `x` shows, swapped. Only these conjunctions: what
    /// an `or` shows when it holds is a disjunction, which facts cannot say
    /// (that waits on logical types, PLAN.md Q7).
    pub(crate) fn test_facts(&self, test: ExpId) -> (Vec<SizeFact>, Vec<SizeFact>) {
        let none = (vec![], vec![]);
        if let Exp::If { test: a, then, els } = self.arena.exp_at(test) {
            let (ta, ea) = self.test_facts(*a);
            if matches!(self.arena.exp_at(*then), Exp::Bool(true)) {
                let (_, eb) = self.test_facts(*els);
                return (vec![], [ea, eb].concat());
            }
            if matches!(self.arena.exp_at(*els), Exp::Bool(false)) {
                let (tb, _) = self.test_facts(*then);
                return ([ta, tb].concat(), vec![]);
            }
            return none;
        }
        let Exp::App { fun, args } = self.arena.exp_at(test) else { return none };
        if let (Some(op), [x]) = (self.standard_ref(*fun), &args[..])
            && self.interner.name(op) == "not"
        {
            let (t, e) = self.test_facts(*x);
            return (e, t);
        }
        // What the callee's type says it proves of sizes (`Prop::Rel`), as
        // the facts each relation is.
        let Some((then, els, args)) = self.latent_props(test) else { return none };
        (self.rel_facts(&then, &args), self.rel_facts(&els, &args))
    }

    /// The size facts relations `props` are, of `args`: `a < b` is `b - a -
    /// 1 ≥ 0`; `a ≤ b`, `b - a ≥ 0`; `a = b`, `a - b = 0`; `a ≠ b`, of a
    /// natural and 0, the other's `- 1 ≥ 0`, and of others nothing. A
    /// relation of a size not known (not a natural's, not a `nlist`'s)
    /// says nothing.
    fn rel_facts(&self, props: &[crate::ast::Prop], args: &[ExpId]) -> Vec<SizeFact> {
        use crate::ast::{Prop, Rel, Term};
        let term = |t: &Term| -> Option<Size> {
            let s = match t {
                Term::Param(i) => self.nat_size(*args.get(*i)?)?,
                Term::Lit(k) => Size::lit(*k),
                Term::Length(i) => {
                    let Exp::Var(v) = self.arena.exp_at(*args.get(*i)?) else { return None };
                    match self.arena.get(self.arena.resolve(self.lookup(*v)?)) {
                        Ty::NList { size, .. } => size.clone(),
                        _ => return None,
                    }
                }
            };
            matches!(s, Size::Lin { .. }).then_some(s)
        };
        let ge = |lin: Size| SizeFact { lin, eq: false };
        let mut out = Vec::new();
        for p in props {
            let Prop::Rel { op, a, b } = p else { continue };
            let (Some(x), Some(y)) = (term(a), term(b)) else { continue };
            match op {
                Rel::Lt => out.push(ge(y.add_scaled(&x, -1).plus(-1))),
                Rel::Le => out.push(ge(y.add_scaled(&x, -1))),
                Rel::Eq => out.push(SizeFact { lin: x.add_scaled(&y, -1), eq: true }),
                Rel::Ne => match (x.as_lit(), y.as_lit()) {
                    (_, Some(0)) => out.push(ge(x.plus(-1))),
                    (Some(0), _) => out.push(ge(y.plus(-1))),
                    _ => {}
                },
            }
        }
        out
    }

    /// `(+ a b)` and `(- a b)` of naturals: a natural of the sum, and of the
    /// difference where the facts show it no less than 0. `None` for any
    /// other call, which is then an ordinary one.
    pub(crate) fn nat_arith(&self, op: &str, a: &Size, b: &Size) -> Option<Size> {
        match op {
            "+" => Some(a.add_scaled(b, 1)),
            "-" if !matches!(a, Size::Finite) && self.size_nonneg(&a.add_scaled(b, -1)) => Some(a.add_scaled(b, -1)),
            _ => None,
        }
    }

    /// The least type above two naturals of sizes not shown equal: a `nat`.
    pub(crate) fn nat_join(&mut self, a: TyId, b: TyId) -> Option<TyId> {
        let nat = |c: &Self, t: TyId| matches!(c.arena.get(c.arena.resolve(t)), Ty::Nat(_));
        (nat(self, a) && nat(self, b)).then(|| self.arena.ty(Ty::Nat(Size::Finite)))
    }

    /// A size binder instantiated as `finite` is sound only where it stands
    /// for one size a caller supplies (`docs/research/soundness-findings.md`,
    /// F4): as the size of at most one parameter, that parameter's own
    /// `(nlist T v)` or `(nat v)` (less a constant, perhaps), and nowhere else
    /// a caller supplies or can write. Its occurrences in what the callee
    /// gives back only forget a size. Anything else is an error.
    pub(crate) fn check_finite_sizes(
        &self,
        kinds: &[(DVar, Kind)],
        map: &std::collections::HashMap<DVar, D>,
        body: TyId,
        span: fixpt_read::Span,
    ) -> crate::error::R<()> {
        for (v, k) in kinds {
            // A size binder solved from `v + k` against a size is that size
            // less `k`: a natural only where the facts here show it.
            if *k == Kind::Size
                && let Some(D::Size(s @ Size::Lin { .. })) = map.get(v)
                && !self.size_nonneg(s)
            {
                let name = self.interner.name(self.arena.dvar_name(*v));
                return Err(crate::error::FxError::at(
                    span,
                    format!(
                        "the size `{name}` would be {}, which is not known here to be no less than 0: an argument may be shorter than this procedure's type needs",
                        self.show_size(s)
                    ),
                ));
            }
            if *k == Kind::Size && matches!(map.get(v), Some(D::Size(Size::Finite))) && !self.finite_size_ok(body, *v) {
                let name = self.interner.name(self.arena.dvar_name(*v));
                return Err(crate::error::FxError::at(
                    span,
                    format!(
                        "the size `{name}` cannot be `finite` here: `{name}` is the size of more than one argument, or of something inside one, and `finite` would not keep them the same"
                    ),
                ));
            }
        }
        Ok(())
    }

    fn finite_size_ok(&self, body: TyId, v: DVar) -> bool {
        // `v` less a constant: every length it could stand for is a size.
        let alone = |s: &Size| matches!(s, Size::Lin { k, terms } if *k <= 0 && terms[..] == [(v, 1)]);
        let (mut bad, mut top) = (0, 0);
        let mut seen = HashSet::new();
        match self.arena.get(self.arena.resolve(body)).clone() {
            Ty::Subr { params, result, .. } => {
                for p in params {
                    match self.arena.get(self.arena.resolve(p)).clone() {
                        Ty::Nat(s) if alone(&s) => top += 1,
                        Ty::NList { elem, size, .. } if alone(&size) => {
                            top += 1;
                            self.size_walk(elem, Polarity::Neg, v, &mut bad, &mut seen);
                        }
                        _ => self.size_walk(p, Polarity::Neg, v, &mut bad, &mut seen),
                    }
                }
                self.size_walk(result, Polarity::Pos, v, &mut bad, &mut seen);
            }
            _ => self.size_walk(body, Polarity::Pos, v, &mut bad, &mut seen),
        }
        bad == 0 && top <= 1
    }

    /// Count in `bad` the occurrences of size variable `v` in `t` that a
    /// caller supplies or can write: not in positive position.
    fn size_walk(&self, t: TyId, pol: Polarity, v: DVar, bad: &mut usize, seen: &mut HashSet<(TyId, Polarity)>) {
        let t = self.arena.resolve(t);
        if !seen.insert((t, pol)) {
            return;
        }
        let size = |s: &Size, pol: Polarity, bad: &mut usize| {
            if pol != Polarity::Pos && matches!(s, Size::Lin { terms, .. } if terms.iter().any(|(w, _)| *w == v)) {
                *bad += 1;
            }
        };
        match self.arena.get(t).clone() {
            Ty::Nat(s) => size(&s, pol, bad),
            Ty::NList { elem, size: s, .. } => {
                size(&s, pol, bad);
                self.size_walk(elem, pol, v, bad, seen);
            }
            Ty::Module { descs, vals, .. } => {
                for (_, x) in descs {
                    self.size_walk(x, Polarity::Inv, v, bad, seen);
                }
                for (_, x) in vals {
                    self.size_walk(x, pol, v, bad, seen);
                }
            }
            Ty::Select(..) | Ty::ParamSel(..) | Ty::Lam { .. } => {}
            // What a description function is given, it may use either way.
            Ty::App { args, .. } => {
                for d in args {
                    match d {
                        D::Size(s) => size(&s, Polarity::Inv, bad),
                        D::Type(x) => self.size_walk(x, Polarity::Inv, v, bad, seen),
                        _ => {}
                    }
                }
            }
            Ty::Named { args, .. } => {
                for d in args {
                    match d {
                        D::Size(s) => size(&s, Polarity::Inv, bad),
                        D::Type(x) => self.size_walk(x, Polarity::Inv, v, bad, seen),
                        _ => {}
                    }
                }
            }
            Ty::Subr { params, result, .. } => {
                for p in params {
                    self.size_walk(p, pol.flip(), v, bad, seen);
                }
                self.size_walk(result, pol, v, bad, seen);
            }
            Ty::Poly { body, .. } => self.size_walk(body, pol, v, bad, seen),
            Ty::Pair(x, y, r, _) => {
                let p = if r.is_frozen() { pol } else { Polarity::Inv };
                self.size_walk(x, p, v, bad, seen);
                self.size_walk(y, p, v, bad, seen);
            }
            Ty::Bloblet { fields, frozen, .. } => {
                for f in fields {
                    self.size_walk(f, if frozen { pol } else { Polarity::Inv }, v, bad, seen);
                }
            }
            Ty::Product(ps) | Ty::Sum(ps) => {
                for (_, x) in ps {
                    self.size_walk(x, pol, v, bad, seen);
                }
            }
            Ty::Union(ms) => {
                for x in ms {
                    self.size_walk(x, pol, v, bad, seen);
                }
            }
            Ty::Ref(x, _) | Ty::Array(x, _) | Ty::ICell(x, _) | Ty::MarkKey(x, _) => self.size_walk(x, Polarity::Inv, v, bad, seen),
            Ty::PromptTag { answer: x, payload: y, .. } | Ty::Composable { arg: x, answer: y, .. } => {
                self.size_walk(x, Polarity::Inv, v, bad, seen);
                self.size_walk(y, Polarity::Inv, v, bad, seen);
            }
            Ty::Base(_) | Ty::Void | Ty::Nil | Ty::False | Ty::Proving { .. } | Ty::Var(_) | Ty::Place(_) | Ty::Link(_) => {}
        }
    }

    /// `t` for a variable being bound to it: a `nat` of no known size is
    /// given one, a variable of its own, named after the variable, so that
    /// tests of it can teach facts. The variable is pushed on `skolems`.
    pub(crate) fn name_nat(&mut self, name: Sym, t: TyId) -> TyId {
        // A module's abstract types are named too, for this binding.
        if matches!(self.arena.get(self.arena.resolve(t)), Ty::Module { .. }) {
            return self.name_module(name, t);
        }
        if !matches!(self.arena.get(self.arena.resolve(t)), Ty::Nat(Size::Finite)) {
            return t;
        }
        let v = self.arena.dvar_of(name, Kind::Size);
        self.skolems.push(v);
        self.arena.ty(Ty::Nat(Size::var(v)))
    }

    /// `t` with the sizes named since `depth` forgotten, as `finite`: they
    /// mean nothing outside the scope that named them. Pops them. Each
    /// stands for one value's size, which no caller chooses, so it may be
    /// forgotten only where `t` gives it back: where a caller would supply
    /// something of that size, forgetting it would let any size in
    /// (`docs/research/soundness-findings.md`, F8), and that is an error.
    pub(crate) fn forget_nats(&mut self, depth: usize, t: TyId, span: fixpt_read::Span) -> crate::error::R<TyId> {
        if self.skolems.len() == depth {
            return Ok(t);
        }
        let mut named: Vec<DVar> = self.skolems.drain(depth..).collect();
        // A module's abstract type cannot be forgotten: nothing may leave
        // its binding's scope still mentioning it.
        if let Some(v) = named.iter().find(|v| self.is_module_var(**v) && self.mentions_var(t, **v)) {
            let name = self.interner.name(self.arena.dvar_name(*v)).to_string();
            return Err(crate::error::FxError::at(
                span,
                format!("this is a {}, and `{name}` is a module's abstract type, not known outside the scope where the module is named", self.show_ty(t)),
            ));
        }
        named.retain(|v| !self.is_module_var(*v));
        for v in &named {
            let mut bad = 0;
            self.size_walk(t, Polarity::Pos, *v, &mut bad, &mut HashSet::new());
            if bad > 0 {
                let name = self.interner.name(self.arena.dvar_name(*v)).to_string();
                return Err(crate::error::FxError::at(
                    span,
                    format!(
                        "this is a {}, which takes something of the size of `{name}`, and that size is not known outside `{name}`'s scope",
                        self.show_ty(t)
                    ),
                ));
            }
        }
        let map: std::collections::HashMap<DVar, D> = named.into_iter().map(|v| (v, D::Size(Size::Finite))).collect();
        Ok(self.subst(t, &map))
    }
}
