//! Subtyping, subeffecting and subregioning — `inequal.lisp`.
//!
//! This file is what FX-87 has instead of inference. FX-91 reconciles two
//! descriptions by *unifying* them, making them equal; FX-87 asks the weaker
//! question, whether one will do where the other was wanted, and that question
//! has three answers because it has three kinds.
//!
//! * **Regions.** `r ≤ R` when `r` is one of the regions `R` unions together.
//! * **Effects.** `e₁ ≤ e₂` when every atom of `e₁` is covered by an atom of
//!   `e₂` with the same constructor over a larger region. `pure` is below
//!   everything, which is the whole point of tracking effects at all.
//! * **Types.** Structural, and the variances are the interesting part:
//!   a `subr`'s **arguments are contravariant** and its result covariant, and a
//!   `ref` is **invariant in what it holds** unless both sides are immutable —
//!   because a mutable cell can be written through, and a covariant mutable
//!   cell is the classic unsoundness.
//!
//! # `dstore`, and why comparison needs one
//!
//! Two `poly` types can be equal while binding different names. The reference
//! compares them by renaming both sides' binders to the same fresh names in a
//! `dstore`, which is a substitution carried *per side*. That is why every
//! function here takes two of everything: the two descriptions may come from
//! different scopes and mean different things by the same symbol.
//!
//! # `trail`, and why comparison terminates
//!
//! Types contain themselves, so the recursion would not. `type-less-1?` keeps
//! a trail of the pairs it is already in the middle of comparing and answers
//! `#t` on meeting one again — coinduction, in the form of an occurs list.

use crate::ast::{Arena, Desc, DescId, Kind};
use fixpt_read::Sym;
use std::collections::HashMap;

/// A per-side renaming of description variables, for comparing `poly` types.
pub type DStore = HashMap<Sym, Sym>;

/// The region an immutable value lives in.
///
/// `@=` is not merely one region among many: it is the one where a `ref` may be
/// compared covariantly, because nothing can write through it.
pub const IMMUTABLE_REGION: &str = "@=";

pub struct Rel<'a> {
    arena: &'a Arena,
    /// `@=`, the region where a `ref` may be compared covariantly.
    immutable: Sym,
    /// The name of the `ref` constructor, so its special variance can be
    /// recognised without hard-coding a string here.
    ref_name: Sym,
}

impl<'a> Rel<'a> {
    pub fn new(arena: &'a Arena, immutable: Sym, ref_name: Sym) -> Rel<'a> {
        Rel { arena, immutable, ref_name }
    }

    fn get(&self, id: DescId) -> &Desc {
        self.arena.get(id)
    }

    fn rename(&self, s: Sym, store: &DStore) -> Sym {
        store.get(&s).copied().unwrap_or(s)
    }

    // ------------------------------------------------------------ regions
    /// `r1 ≤ r2`: `r2` names at least the regions `r1` does.
    pub fn region_less(&self, r1: DescId, r2: DescId, d1: &DStore, d2: &DStore) -> bool {
        let members2: Vec<DescId> = match self.get(r2) {
            Desc::RUnion(parts) => parts.clone(),
            _ => vec![r2],
        };
        match self.get(r1) {
            Desc::RUnion(parts) => {
                let parts = parts.clone();
                parts.iter().all(|p| {
                    members2.iter().any(|q| self.region_equal(*p, *q, d1, d2))
                })
            }
            _ => members2.iter().any(|q| self.region_equal(r1, *q, d1, d2)),
        }
    }

    pub fn region_equal(&self, r1: DescId, r2: DescId, d1: &DStore, d2: &DStore) -> bool {
        match (self.get(r1), self.get(r2)) {
            (Desc::Var(a), Desc::Var(b)) => self.rename(*a, d1) == self.rename(*b, d2),
            (Desc::Con(a, xs), Desc::Con(b, ys)) if xs.is_empty() && ys.is_empty() => a == b,
            _ => {
                self.region_less_sets(r1, r2, d1, d2) && self.region_less_sets(r2, r1, d2, d1)
            }
        }
    }

    fn region_less_sets(&self, r1: DescId, r2: DescId, d1: &DStore, d2: &DStore) -> bool {
        let members1: Vec<DescId> = match self.get(r1) {
            Desc::RUnion(parts) => parts.clone(),
            _ => vec![r1],
        };
        let members2: Vec<DescId> = match self.get(r2) {
            Desc::RUnion(parts) => parts.clone(),
            _ => vec![r2],
        };
        members1.iter().all(|p| {
            members2.iter().any(|q| match (self.get(*p), self.get(*q)) {
                (Desc::Var(a), Desc::Var(b)) => self.rename(*a, d1) == self.rename(*b, d2),
                (Desc::Con(a, xs), Desc::Con(b, ys)) if xs.is_empty() && ys.is_empty() => a == b,
                _ => false,
            })
        })
    }

    fn is_immutable(&self, r: DescId, store: &DStore) -> bool {
        match self.get(r) {
            Desc::Con(name, args) if args.is_empty() => *name == self.immutable,
            Desc::Var(v) => self.rename(*v, store) == self.immutable,
            _ => false,
        }
    }

    // ------------------------------------------------------------ effects
    /// `e1 ≤ e2`. Both are assumed in the normal form [`Arena::maxeff`]
    /// produces — flattened, `pure`-free, deduplicated — which is what
    /// `effect-less-1?` says it relies on.
    pub fn effect_less(&self, e1: DescId, e2: DescId, d1: &DStore, d2: &DStore) -> bool {
        let atoms2: Vec<DescId> = match self.get(e2) {
            Desc::MaxEff(parts) => parts.clone(),
            _ => vec![e2],
        };
        match self.get(e1) {
            // Nothing is below `pure`, and `pure` is below everything.
            Desc::Pure => true,
            Desc::MaxEff(parts) => {
                let parts = parts.clone();
                parts.iter().all(|p| self.effect_less(*p, e2, d1, d2))
            }
            Desc::Read(r) => self.covered(*r, &atoms2, d1, d2, EffectKind::Read),
            Desc::Write(r) => self.covered(*r, &atoms2, d1, d2, EffectKind::Write),
            Desc::Alloc(r) => self.covered(*r, &atoms2, d1, d2, EffectKind::Alloc),
            // An effect variable is only below itself.
            Desc::Var(v) => atoms2.iter().any(|a| match self.get(*a) {
                Desc::Var(w) => self.rename(*v, d1) == self.rename(*w, d2),
                _ => false,
            }),
            _ => atoms2.iter().any(|a| self.desc_equal(e1, *a, d1, d2)),
        }
    }

    /// Is `region` within the region of the same-constructor atom on the right?
    fn covered(
        &self,
        region: DescId,
        atoms2: &[DescId],
        d1: &DStore,
        d2: &DStore,
        want: EffectKind,
    ) -> bool {
        atoms2.iter().any(|a| match (want, self.get(*a)) {
            (EffectKind::Read, Desc::Read(r2))
            | (EffectKind::Write, Desc::Write(r2))
            | (EffectKind::Alloc, Desc::Alloc(r2)) => self.region_less(region, *r2, d1, d2),
            _ => false,
        })
    }

    pub fn effect_equal(&self, e1: DescId, e2: DescId, d1: &DStore, d2: &DStore) -> bool {
        self.effect_less(e1, e2, d1, d2) && self.effect_less(e2, e1, d2, d1)
    }

    // -------------------------------------------------------------- types
    pub fn type_less(&self, t1: DescId, t2: DescId, d1: &DStore, d2: &DStore) -> bool {
        self.type_less_trail(t1, t2, d1, d2, &mut Vec::new())
    }

    fn type_less_trail(
        &self,
        t1: DescId,
        t2: DescId,
        d1: &DStore,
        d2: &DStore,
        trail: &mut Vec<(DescId, DescId)>,
    ) -> bool {
        if trail.contains(&(t1, t2)) {
            return true;
        }
        trail.push((t1, t2));
        let result = self.type_less_inner(t1, t2, d1, d2, trail);
        trail.pop();
        result
    }

    fn type_less_inner(
        &self,
        t1: DescId,
        t2: DescId,
        d1: &DStore,
        d2: &DStore,
        trail: &mut Vec<(DescId, DescId)>,
    ) -> bool {
        match (self.get(t1), self.get(t2)) {
            (Desc::Var(a), Desc::Var(b)) => self.rename(*a, d1) == self.rename(*b, d2),

            // `ref` is the one that has to be got right. Writing through a
            // reference means its contents cannot vary covariantly, so the
            // types must be *equal* — unless both cells are immutable, where
            // no write is possible and covariance is sound.
            (Desc::Con(n1, a1), Desc::Con(n2, a2))
                if self.is_ref(*n1) && self.is_ref(*n2) && a1.len() == 2 && a2.len() == 2 =>
            {
                let (v1, r1, v2, r2) = (a1[0], a1[1], a2[0], a2[1]);
                (self.region_less(r1, r2, d1, d2) && self.type_equal(v1, v2, d1, d2))
                    || (self.is_immutable(r1, d1)
                        && self.is_immutable(r2, d2)
                        && self.type_less_trail(v1, v2, d1, d2, trail))
            }

            // Every other constructor is compared componentwise. The reference
            // reaches `standard-less-1?` here, which is generated from each
            // standard type's declared variance; without those declarations the
            // safe reading is invariance, which is what equality gives.
            (Desc::Con(n1, a1), Desc::Con(n2, a2)) => {
                n1 == n2
                    && a1.len() == a2.len()
                    && a1
                        .clone()
                        .iter()
                        .zip(a2.clone())
                        .all(|(x, y)| self.desc_equal_trail(*x, y, d1, d2, trail))
            }

            (
                Desc::Subr { effect: e1, args: as1, result: r1 },
                Desc::Subr { effect: e2, args: as2, result: r2 },
            ) => {
                as1.len() == as2.len()
                    && self.effect_less(*e1, *e2, d1, d2)
                    // Contravariant: a subroutine accepting more is usable
                    // where one accepting less was wanted.
                    && as1
                        .clone()
                        .iter()
                        .zip(as2.clone())
                        .all(|(x, y)| self.type_less_trail(y, *x, d2, d1, trail))
                    && self.type_less_trail(*r1, *r2, d1, d2, trail)
            }

            (
                Desc::Poly { binders: b1, body: y1 },
                Desc::Poly { binders: b2, body: y2 },
            ) => {
                if b1.len() != b2.len()
                    || !b1.iter().zip(b2).all(|(x, y)| kinds_equal(&x.kind, &y.kind))
                {
                    return false;
                }
                // Rename both sides' binders to a common set, so the bodies can
                // be compared without either side's names mattering.
                let (mut n1, mut n2) = (d1.clone(), d2.clone());
                for (x, y) in b1.iter().zip(b2) {
                    n1.insert(x.name, x.name);
                    n2.insert(y.name, x.name);
                }
                self.type_less_trail(*y1, *y2, &n1, &n2, trail)
            }

            (Desc::RecordOf { fields: f1, region: g1 }, Desc::RecordOf { fields: f2, region: g2 })
            | (Desc::OneOf { variants: f1, region: g1 }, Desc::OneOf { variants: f2, region: g2 }) => {
                f1.len() == f2.len()
                    && f1.clone().iter().zip(f2.clone()).all(|((n1, x), (n2, y))| {
                        *n1 == n2 && self.desc_equal_trail(*x, y, d1, d2, trail)
                    })
                    && self.region_equal(*g1, *g2, d1, d2)
            }

            // Effects and regions reached as components of a type. These are
            // compared *here* rather than by falling through to `desc_equal`,
            // which is defined as subtyping both ways and would recur forever.
            (Desc::Pure, Desc::Pure) => true,
            (Desc::Read(_), Desc::Read(_))
            | (Desc::Write(_), Desc::Write(_))
            | (Desc::Alloc(_), Desc::Alloc(_))
            | (Desc::MaxEff(_), Desc::MaxEff(_)) => {
                self.effect_equal(t1, t2, d1, d2)
            }
            (Desc::RUnion(_), _) | (_, Desc::RUnion(_)) => self.region_equal(t1, t2, d1, d2),
            (
                Desc::Vsubr { effect: e1, args: a1, rest: s1, result: r1 },
                Desc::Vsubr { effect: e2, args: a2, rest: s2, result: r2 },
            ) => {
                self.effect_less(*e1, *e2, d1, d2)
                    && a1.len() == a2.len()
                    && a1
                        .clone()
                        .iter()
                        .zip(a2.clone())
                        .all(|(x, y)| self.type_less_trail(y, *x, d2, d1, trail))
                    && self.type_less_trail(*s2, *s1, d2, d1, trail)
                    && self.type_less_trail(*r1, *r2, d1, d2, trail)
            }
            (Desc::DApp { fun: f1, args: a1 }, Desc::DApp { fun: f2, args: a2 }) => {
                a1.len() == a2.len()
                    && self.type_less_trail(*f1, *f2, d1, d2, trail)
                    && a1
                        .clone()
                        .iter()
                        .zip(a2.clone())
                        .all(|(x, y)| self.desc_equal_trail(*x, y, d1, d2, trail))
            }
            (Desc::DAbs { binders: b1, body: y1 }, Desc::DAbs { binders: b2, body: y2 }) => {
                b1.len() == b2.len()
                    && b1.iter().zip(b2).all(|(x, y)| kinds_equal(&x.kind, &y.kind))
                    && self.type_less_trail(*y1, *y2, d1, d2, trail)
            }
            _ => false,
        }
    }

    fn is_ref(&self, name: Sym) -> bool {
        self.ref_name == name
    }

    pub fn type_equal(&self, t1: DescId, t2: DescId, d1: &DStore, d2: &DStore) -> bool {
        self.desc_equal(t1, t2, d1, d2)
    }

    pub fn desc_equal(&self, t1: DescId, t2: DescId, d1: &DStore, d2: &DStore) -> bool {
        self.desc_equal_trail(t1, t2, d1, d2, &mut Vec::new())
    }

    fn desc_equal_trail(
        &self,
        t1: DescId,
        t2: DescId,
        d1: &DStore,
        d2: &DStore,
        trail: &mut Vec<(DescId, DescId)>,
    ) -> bool {
        self.type_less_trail(t1, t2, d1, d2, trail) && self.type_less_trail(t2, t1, d2, d1, trail)
    }
}

#[derive(Copy, Clone, PartialEq, Eq)]
enum EffectKind {
    Read,
    Write,
    Alloc,
}

pub fn kinds_equal(a: &Kind, b: &Kind) -> bool {
    a == b
}
