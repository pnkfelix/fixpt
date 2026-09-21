//! Subtyping and subeffecting — `description<=?` in `unify.scm`.
//!
//! Used by `the` and `does`, the two forms that assert a description and must
//! accept anything more precise. Subroutines are contravariant in their
//! parameters, as usual; effects compare by subset, which under algebraic
//! reconstruction is expressed by adding a *slack* variable and asking the
//! solver whether `slack ∪ e1 = e2` can hold.

use crate::ast::{Fx, FxId, Kind};
use crate::check::{kind_eq, Checker};
use crate::error::R;
use crate::unify::Mode;

impl Checker {
    /// `description<=?`
    pub fn description_leq(&mut self, a: FxId, b: FxId) -> R<bool> {
        self.unify_env.clear();
        self.leq(a, b)
    }

    fn leq(&mut self, a: FxId, b: FxId) -> R<bool> {
        let a = self.p.arena.find(a);
        let b = self.p.arena.find(b);
        if a == b {
            return Ok(true);
        }
        match self.p.arena.get(a).clone() {
            Fx::Variable(_) => {
                // An effect variable is the singleton effect containing it.
                if kind_eq(&self.kind_of_dexp(a)?, &Kind::Effect) {
                    let span = self.p.arena.span(a);
                    let singleton = self.p.arena.add(span, Fx::MaxEff(vec![a]));
                    return self.leq(singleton, b);
                }
                self.unify_1(Mode::Unify, a, b)
            }
            Fx::DLambda { .. } => self.dlambda_leq(a, b),
            Fx::Select { .. } => self.unify_1(Mode::VariableEq, a, b),
            Fx::MaxEff(_) => self.maxeff_leq(a, b),
            Fx::Subr { .. } => self.subr_leq(a, b),
            Fx::Poly { .. } => self.unify_1(Mode::Unify, a, b),
            Fx::PolyTilde { .. } => Err(crate::error::FxError::fatal(
                self.p.arena.span(a),
                "trying to compare type schemes",
            )),
            Fx::SumOf { .. } => self.sumof_leq(a, b),
            Fx::ProductOf { .. } => self.productof_leq(a, b),
            Fx::ModuleOf { .. } => self.moduleof_leq(a, b),
            _ => self.unify_1(Mode::Unify, a, b),
        }
    }

    /// Reproduces a second bug in the 1991 source.
    ///
    /// `dlambda<=?` recurses with *itself* on the bodies rather than with
    /// `description<=-1?`. Since a dlambda's body is a type and not another
    /// dlambda, the recursion fails immediately, so two dlambdas essentially
    /// never compare. Preserved for the same reason as `unify_poly`'s bug: the
    /// reference defines what FX-91 accepts. See `docs/divergences.md`.
    fn dlambda_leq(&mut self, a: FxId, b: FxId) -> R<bool> {
        let (ids1, kinds1, body1) = match self.p.arena.get(a).clone() {
            Fx::DLambda { ids, kinds, body } => (ids, kinds, body),
            _ => return Ok(false),
        };
        let (ids2, kinds2, body2) = match self.p.arena.get(b).clone() {
            Fx::DLambda { ids, kinds, body } => (ids, kinds, body),
            _ => return Ok(false),
        };
        if ids1.len() != ids2.len() || !kinds1.iter().zip(&kinds2).all(|(x, y)| kind_eq(x, y)) {
            return Ok(false);
        }
        self.unify_env_pairs(&ids1, &ids2);
        self.dlambda_leq(body1, body2)
    }

    fn maxeff_leq(&mut self, a: FxId, b: FxId) -> R<bool> {
        let members = match self.p.arena.get(a) {
            Fx::MaxEff(e) => e.clone(),
            _ => return Ok(false),
        };
        // The empty effect is below everything.
        if members.is_empty() {
            return Ok(true);
        }
        if self.algebraic {
            let span = self.p.arena.span(a);
            // `slack ∪ a = b` is satisfiable exactly when a ⊆ b.
            let slack = {
                                self.fresh_unification(span, true, Kind::Effect)
            };
            let union = self.p.arena.add(span, Fx::MaxEff(vec![slack, a]));
            return self.add_constraint(union, b);
        }
        // Without the solver: force every unification variable to `pure`, then
        // require containment outright.
        let span = self.p.arena.span(a);
        let empty = self.pure(span);
        let mut frees = crate::free::free_dvars_of_dexp(&mut self.p.arena, a);
        frees.extend(crate::free::free_dvars_of_dexp(&mut self.p.arena, b));
        for f in frees {
            if self.p.arena.var(f).is_some_and(|v| v.is_unification())
                && !self.unify_1(Mode::Unify, f, empty)?
            {
                return Ok(false);
            }
        }
        let fa = crate::free::free_dvars_of_dexp(&mut self.p.arena, a);
        let fb = crate::free::free_dvars_of_dexp(&mut self.p.arena, b);
        Ok(fa.iter().all(|x| fb.iter().any(|y| self.p.arena.same_variable(*x, *y))))
    }

    /// Contravariant in parameters, covariant in result and latent effect.
    fn subr_leq(&mut self, a: FxId, b: FxId) -> R<bool> {
        let (e1, ids1, types1, body1) = match self.p.arena.get(a).clone() {
            Fx::Subr { effect, ids, types, body } => (effect, ids, types, body),
            _ => return Ok(false),
        };
        let (e2, ids2, types2, body2) = match self.p.arena.get(b).clone() {
            Fx::Subr { effect, ids, types, body } => (effect, ids, types, body),
            _ => return Ok(false),
        };
        self.unify_env_pairs(&ids1, &ids2);
        if ids1.len() != ids2.len() {
            return Ok(false);
        }
        if !self.leq(e1, e2)? {
            return Ok(false);
        }
        for (t2, t1) in types2.iter().zip(&types1) {
            if !self.leq(*t2, *t1)? {
                return Ok(false);
            }
        }
        self.leq(body1, body2)
    }

    /// A sum may have *fewer* variants than its supertype.
    fn sumof_leq(&mut self, a: FxId, b: FxId) -> R<bool> {
        let (tags1, types1) = match self.p.arena.get(a).clone() {
            Fx::SumOf { tags, types } => (tags, types),
            _ => return Ok(false),
        };
        let (tags2, types2) = match self.p.arena.get(b).clone() {
            Fx::SumOf { tags, types } => (tags, types),
            _ => return Ok(false),
        };
        if tags1.len() > tags2.len() {
            return Ok(false);
        }
        for (t1, ty1) in tags1.iter().zip(&types1) {
            let mut ok = false;
            for (t2, ty2) in tags2.iter().zip(&types2) {
                if t1 == t2 && self.leq(*ty2, *ty1)? {
                    ok = true;
                    break;
                }
            }
            if !ok {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// A product may have *more* fields than its supertype, and the
    /// supertype's must come first.
    fn productof_leq(&mut self, a: FxId, b: FxId) -> R<bool> {
        let (tags1, types1) = match self.p.arena.get(a).clone() {
            Fx::ProductOf { tags, types } => (tags, types),
            _ => return Ok(false),
        };
        let (tags2, types2) = match self.p.arena.get(b).clone() {
            Fx::ProductOf { tags, types } => (tags, types),
            _ => return Ok(false),
        };
        if tags1.len() < tags2.len() || !tags2.iter().zip(&tags1).all(|(x, y)| x == y) {
            return Ok(false);
        }
        for (t2, ty2) in tags2.iter().zip(&types2) {
            let mut ok = false;
            for (t1, ty1) in tags1.iter().zip(&types1) {
                if t1 == t2 && self.leq(*ty1, *ty2)? {
                    ok = true;
                    break;
                }
            }
            if !ok {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// A module may export *more* than its supertype requires.
    fn moduleof_leq(&mut self, a: FxId, b: FxId) -> R<bool> {
        let (abs1, kinds1, val1, types1) = match self.p.arena.get(a).clone() {
            Fx::ModuleOf { abs_ids, abs_kinds, val_ids, val_types, .. } => {
                (abs_ids, abs_kinds, val_ids, val_types)
            }
            _ => return Ok(false),
        };
        let (abs2, kinds2, val2, types2) = match self.p.arena.get(b).clone() {
            Fx::ModuleOf { abs_ids, abs_kinds, val_ids, val_types, .. } => {
                (abs_ids, abs_kinds, val_ids, val_types)
            }
            _ => return Ok(false),
        };
        self.match_moduleof_by_name(a, b);
        if abs1.len() < abs2.len() || val1.len() < val2.len() {
            return Ok(false);
        }
        for (i2, k2) in abs2.iter().zip(&kinds2) {
            let found = abs1.iter().zip(&kinds1).any(|(i1, k1)| {
                self.same_after_unify_env(*i1, *i2) && kind_eq(k1, k2)
            });
            if !found {
                return Ok(false);
            }
        }
        for (i2, t2) in val2.iter().zip(&types2) {
            let mut ok = false;
            for (i1, t1) in val1.iter().zip(&types1) {
                if self.same_after_unify_env(*i1, *i2) && self.leq(*t1, *t2)? {
                    ok = true;
                    break;
                }
            }
            if !ok {
                return Ok(false);
            }
        }
        Ok(true)
    }
}
