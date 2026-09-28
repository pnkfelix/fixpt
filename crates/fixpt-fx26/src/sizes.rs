//! Sizes: linear expressions over size variables, and what the facts in
//! scope show about them (`docs/research/sizes.md`, N5b).
//!
//! A fact is `lin = 0` or `lin ≥ 0`, learned in a branch: `(null? xs)` with
//! `xs : (nlist T n)` gives `n = 0` in the `then` and `n - 1 ≥ 0` in the
//! `else`. An equality is used to rewrite a variable away; an inequality is
//! used as it is, or with a constant to spare.

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
        plainly(&a) || self.size_facts.iter().filter(|f| !f.eq).any(|f| plainly(&a.add_scaled(&self.reduced(&f.lin), -1)))
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
            Exp::App { fun, .. } => matches!(self.arena.exp_at(*fun),
                Exp::Var(op) if matches!(self.interner.name(*op), "+" | "-" | "length" | "string-length" | "array-length") && self.is_standard(*op)),
            _ => false,
        }
    }

    /// What `test` shows about sizes when it holds, and when not.
    /// `(null? xs)`, `xs : (nlist T n)`: `n = 0`, or `n - 1 ≥ 0`. A
    /// comparison of naturals: `(< a b)`, `b - a - 1 ≥ 0`, or `a - b ≥ 0`;
    /// `(= a 0)`, `a = 0`, or, a natural not 0, `a - 1 ≥ 0`.
    pub(crate) fn test_facts(&self, test: ExpId) -> (Vec<SizeFact>, Vec<SizeFact>) {
        let none = (vec![], vec![]);
        let Exp::App { fun, args } = self.arena.exp_at(test) else { return none };
        let Exp::Var(op) = self.arena.exp_at(*fun) else { return none };
        if !self.is_standard(*op) {
            return none;
        }
        let ge = |lin: Size| vec![SizeFact { lin, eq: false }];
        match (self.interner.name(*op), &args[..]) {
            ("null?", [a]) => {
                let Exp::Var(v) = self.arena.exp_at(*a) else { return none };
                let Some(t) = self.lookup(*v) else { return none };
                match self.arena.get(self.arena.resolve(t)) {
                    Ty::NList { size: n @ Size::Lin { .. }, .. } => (vec![SizeFact { lin: n.clone(), eq: true }], ge(n.plus(-1))),
                    _ => none,
                }
            }
            (op @ ("<" | "<=" | ">" | ">=" | "="), [a, b]) => {
                let (Some(x @ Size::Lin { .. }), Some(y @ Size::Lin { .. })) = (self.nat_size(*a), self.nat_size(*b)) else { return none };
                // `a < b` is `b - a - 1 ≥ 0`; `a ≤ b`, `b - a ≥ 0`.
                let lt = |x: &Size, y: &Size| ge(y.add_scaled(x, -1).plus(-1));
                let le = |x: &Size, y: &Size| ge(y.add_scaled(x, -1));
                match op {
                    "<" => (lt(&x, &y), le(&y, &x)),
                    "<=" => (le(&x, &y), lt(&y, &x)),
                    ">" => (lt(&y, &x), le(&x, &y)),
                    ">=" => (le(&y, &x), lt(&x, &y)),
                    _ => {
                        let no = match (x.as_lit(), y.as_lit()) {
                            (_, Some(0)) => ge(x.plus(-1)),
                            (Some(0), _) => ge(y.plus(-1)),
                            _ => vec![],
                        };
                        (vec![SizeFact { lin: x.add_scaled(&y, -1), eq: true }], no)
                    }
                }
            }
            _ => none,
        }
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
            Ty::Pair(x, y, r) => {
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
            Ty::Ref(x, _) | Ty::Array(x, _) | Ty::ICell(x, _) | Ty::MarkKey(x, _) => self.size_walk(x, Polarity::Inv, v, bad, seen),
            Ty::PromptTag { answer: x, payload: y, .. } | Ty::Composable { arg: x, answer: y, .. } => {
                self.size_walk(x, Polarity::Inv, v, bad, seen);
                self.size_walk(y, Polarity::Inv, v, bad, seen);
            }
            Ty::Base(_) | Ty::Void | Ty::Var(_) | Ty::Place(_) | Ty::Link(_) => {}
        }
    }

    /// `t` for a variable being bound to it: a `nat` of no known size is
    /// given one, a variable of its own, named after the variable, so that
    /// tests of it can teach facts. The variable is pushed on `skolems`.
    pub(crate) fn name_nat(&mut self, name: Sym, t: TyId) -> TyId {
        if !matches!(self.arena.get(self.arena.resolve(t)), Ty::Nat(Size::Finite)) {
            return t;
        }
        let v = self.arena.dvar_of(name, Kind::Size);
        self.skolems.push(v);
        self.arena.ty(Ty::Nat(Size::var(v)))
    }

    /// `t` with the sizes named since `depth` forgotten, as `finite`: they
    /// mean nothing outside the scope that named them. Pops them.
    pub(crate) fn forget_nats(&mut self, depth: usize, t: TyId) -> TyId {
        if self.skolems.len() == depth {
            return t;
        }
        let map: std::collections::HashMap<DVar, D> = self.skolems.drain(depth..).map(|v| (v, D::Size(Size::Finite))).collect();
        self.subst(t, &map)
    }
}
