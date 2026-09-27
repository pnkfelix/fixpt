//! Sizes: linear expressions over size variables, and what the facts in
//! scope show about them (`docs/research/sizes.md`, N5b).
//!
//! A fact is `lin = 0` or `lin ≥ 0`, learned in a branch: `(null? xs)` with
//! `xs : (nlist T n)` gives `n = 0` in the `then` and `n - 1 ≥ 0` in the
//! `else`. An equality is used to rewrite a variable away; an inequality is
//! used as it is, or with a constant to spare.

use std::collections::BTreeMap;

use crate::ast::{D, DVar, Size};
use crate::check::Checker;

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
}
