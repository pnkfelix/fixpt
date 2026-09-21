//! Type and effect inference — `typecheck.scm`.
//!
//! The algorithm is O'Toole's polymorphic type reconstruction plus Jouvelot and
//! Gifford's algebraic reconstruction of effects (POPL '91). Every expression
//! yields a *pair*: its type and the effect evaluating it may have. The two are
//! inferred in one pass, which is why nearly everything here returns
//! `(type, effect)` rather than a type.
//!
//! Generalisation is where the subtlety lives. A `let`-bound value is
//! generalised over the unification variables free in its type — but only when
//! the expression is *non-expansive*, the value restriction, because
//! generalising over an allocation would let one reference be used at two
//! types. [`Checker::expansive`] is FX-91's version of that test.

use crate::ast::{Constraint, Fx, FxId, Kind, VarClass};
use crate::check::{kind_eq, Checker};
use crate::env::TkEntry;
use crate::error::{FxError, R};
use crate::free::{free_dvars_of_dexp, free_dvars_of_free_vars, free_dvars_of_exp};

/// A type paired with the effect of producing it.
pub type TypeEffect = (FxId, FxId);

impl Checker<'_> {
    /// The type alone.
    ///
    /// Keyed on the *type* cache only, deliberately: `evaluate_select` records
    /// a type on a reconstructed module expression without recording an
    /// effect, and this is what lets that type be reused instead of the whole
    /// `with` being re-checked — which would rebuild the expression and lose
    /// the substitution that was the point.
    pub fn type_of_exp(&mut self, id: FxId) -> R<FxId> {
        if let Some(t) = self.p.arena.exp_info(id).ty {
            return Ok(t);
        }
        let (t, e) = self.type_effect_of_exp_1(id)?;
        if self.cache {
            self.p.arena.exp_info_mut(id).ty = Some(t);
            self.p.arena.exp_info_mut(id).effect = Some(e);
        }
        Ok(t)
    }
    pub fn effect_of_exp(&mut self, id: FxId) -> R<FxId> {
        Ok(self.type_effect_of_exp(id)?.1)
    }

    pub fn type_effect_of_exp(&mut self, id: FxId) -> R<TypeEffect> {
        if let (Some(t), Some(e)) = (self.p.arena.exp_info(id).ty, self.p.arena.exp_info(id).effect)
        {
            return Ok((t, e));
        }
        let (t, e) = self.type_effect_of_exp_1(id)?;
        if self.cache {
            self.p.arena.exp_info_mut(id).ty = Some(t);
            self.p.arena.exp_info_mut(id).effect = Some(e);
        }
        Ok((t, e))
    }

    fn type_effect_of_exp_1(&mut self, id: FxId) -> R<TypeEffect> {
        let span = self.p.arena.span(id);
        match self.p.arena.get(id).clone() {
            Fx::Variable(_) => self.type_of_variable(id),
            Fx::Lambda { .. } => self.type_of_lambda(id),
            Fx::Let { .. } => self.type_of_let(id),
            Fx::PLambda { .. } => self.type_of_plambda(id),
            Fx::Proj { .. } => self.type_of_proj(id),
            Fx::Module { .. } => self.type_of_module(id),
            Fx::With { .. } => self.type_of_with(id),
            Fx::Extend { .. } => self.type_of_extend(id),
            Fx::App { .. } => self.type_of_application(id),
            Fx::If { .. } => self.type_of_if(id),
            Fx::Open(_) => self.type_of_open(id),
            Fx::Close(_) => self.type_of_close(id),
            Fx::Begin(_) => self.type_of_begin(id),
            Fx::Load { .. } => self.type_of_load(id),
            Fx::The { .. } => self.type_of_the(id),
            Fx::Does { .. } => self.type_of_does(id),
            Fx::Sum { .. } => self.type_of_sum(id),
            Fx::Product { .. } => self.type_of_product(id),
            Fx::TagCase { .. } => self.type_of_tagcase(id),
            Fx::Extract { .. } => self.type_of_extract(id),
            other => Err(FxError::fatal(
                span,
                format!("unknown expression in type/effect-of: {}", crate::sugar::head_name(&other)),
            )),
        }
    }

    // --------------------------------------------------------------- atoms
    fn type_of_variable(&mut self, id: FxId) -> R<TypeEffect> {
        let span = self.p.arena.span(id);
        let v = self.p.arena.var(id).cloned().expect("a variable");
        self.require(
            v.domain == crate::ast::Domain::Value,
            span,
            "variable isn't a value variable",
        )?;
        let name = self.p.interner.name(v.user_name).to_string();
        let entry = self
            .tk_env
            .get(&v)
            .ok_or_else(|| FxError::user(span, format!("unbound value variable {name}")))?
            .clone();
        let ty = entry
            .as_type()
            .ok_or_else(|| FxError::user(span, format!("{name} has no type")))?;
        // A type scheme is instantiated with fresh unification variables, and
        // the constraints it carried come along with it.
        let real = match self.p.arena.get(ty).clone() {
            Fx::PolyTilde { ids, kinds, body, constraints } => {
                let fresh: Vec<FxId> = kinds
                    .iter()
                    .map(|k| {
                        self.fresh_unification(span, true, k.clone())
                    })
                    .collect();
                for (i, f) in ids.iter().zip(&fresh) {
                    self.store_set(*i, *f);
                }
                if self.algebraic {
                    let evaluated = self.evaluate_constraints(&constraints)?;
                    self.union_constraints(&evaluated)?;
                }
                let instance = self.evaluate(body)?;
                for i in &ids {
                    self.store_remove(*i);
                }
                instance
            }
            _ => ty,
        };
        let pure = self.pure(span);
        Ok((real, pure))
    }

    /// Parameters are processed left to right so that a later parameter's type
    /// can mention an earlier one — dependent subroutines.
    fn type_of_lambda(&mut self, id: FxId) -> R<TypeEffect> {
        let span = self.p.arena.span(id);
        let Fx::Lambda { ids, types, body, .. } = self.p.arena.get(id).clone() else {
            unreachable!()
        };
        let mut arg_types = Vec::with_capacity(types.len());
        for (i, t) in ids.iter().zip(&types) {
            let k = self.kind_of_dexp(*t)?;
            self.require(kind_eq(&k, &Kind::Type), span, "lambda argument isn't a type")?;
            let norm = self.evaluate(*t)?;
            self.tk_set(*i, TkEntry::Type(norm));
            arg_types.push(norm);
        }
        let (body_type, body_effect) = self.type_effect_of_exp(body)?;
        let subr = self.p.arena.add(
            span,
            Fx::Subr { effect: body_effect, ids, types: arg_types, body: body_type },
        );
        let pure = self.pure(span);
        Ok((subr, pure))
    }

    fn type_of_let(&mut self, id: FxId) -> R<TypeEffect> {
        let span = self.p.arena.span(id);
        let Fx::Let { ids, exps, body } = self.p.arena.get(id).clone() else { unreachable!() };
        let mark = self.constraint_mark();
        let mut types = Vec::with_capacity(exps.len());
        let mut effects = Vec::with_capacity(exps.len());
        for e in &exps {
            let (t, ef) = self.type_effect_of_exp(*e)?;
            types.push(t);
            effects.push(ef);
        }
        let new_constraints = self.diff_constraints(mark);
        for ((i, e), (t, ef)) in
            ids.iter().zip(&exps).zip(types.iter().zip(&effects))
        {
            let scheme = self.generalize_over(&new_constraints, *e, *ef, *t)?;
            self.tk_set(*i, TkEntry::Type(scheme));
        }
        let (body_type, body_effect) = self.type_effect_of_exp(body)?;
        for (i, e) in ids.iter().zip(&exps) {
            self.store_set(*i, *e);
        }
        let ty = self.evaluate(body_type)?;
        for i in &ids {
            self.store_remove(*i);
        }
        let mut all = vec![body_effect];
        all.extend(effects);
        let effect = self.p.arena.add(span, Fx::MaxEff(all));
        let effect = self.evaluate(effect)?;
        Ok((ty, effect))
    }

    fn type_of_plambda(&mut self, id: FxId) -> R<TypeEffect> {
        let span = self.p.arena.span(id);
        let Fx::PLambda { ids, kinds, body } = self.p.arena.get(id).clone() else {
            unreachable!()
        };
        for (i, k) in ids.iter().zip(&kinds) {
            self.tk_set(*i, TkEntry::Kind(k.clone()));
        }
        let mark = self.constraint_mark();
        let (body_type, body_effect) = self.type_effect_of_exp(body)?;
        // A polymorphic value's body must be pure: that restriction is what
        // makes fully orthogonal polymorphism implementable in the presence of
        // side effects, and the report calls it out as such.
        let pure = self.pure(span);
        let ok = if self.algebraic {
            self.add_constraint(body_effect, pure)?
        } else {
            self.unify(body_effect, pure)?
        };
        self.require(ok, span, "plambda body should be pure")?;
        // Duplicate the constraints introduced inside, so the body stays
        // polymorphic rather than being pinned by one use.
        let inner = self.diff_constraints(mark);
        let duplicated = self.evaluate_constraints(&inner)?;
        self.union_constraints(&duplicated)?;
        let poly = self.p.arena.add(span, Fx::Poly { ids, kinds, body: body_type });
        let pure = self.pure(span);
        Ok((poly, pure))
    }

    fn type_of_proj(&mut self, id: FxId) -> R<TypeEffect> {
        let span = self.p.arena.span(id);
        let Fx::Proj { exp, descs } = self.p.arena.get(id).clone() else { unreachable!() };
        let (poly_type, effect) = self.type_effect_of_exp(exp)?;
        let Fx::Poly { ids, body, .. } = self.p.arena.get(poly_type).clone() else {
            return Err(FxError::user(span, "proj should be applied to a polymorphic value"));
        };
        let mut kinds = Vec::with_capacity(descs.len());
        for d in &descs {
            kinds.push(self.kind_of_dexp(*d)?);
        }
        for (i, k) in ids.iter().zip(&kinds) {
            self.tk_set(*i, TkEntry::Kind(k.clone()));
        }
        for (i, d) in ids.iter().zip(&descs) {
            let norm = self.evaluate(*d)?;
            self.store_set(*i, norm);
        }
        if self.algebraic {
            let cs = self.constraints.clone();
            self.constraints = self.evaluate_constraints(&cs)?;
        }
        let ty = self.evaluate(body)?;
        for i in &ids {
            self.store_remove(*i);
        }
        Ok((ty, effect))
    }

    fn type_of_if(&mut self, id: FxId) -> R<TypeEffect> {
        let span = self.p.arena.span(id);
        let Fx::If { test, then, els } = self.p.arena.get(id).clone() else { unreachable!() };
        let (test_t, test_e) = self.type_effect_of_exp(test)?;
        let (then_t, then_e) = self.type_effect_of_exp(then)?;
        let (else_t, else_e) = self.type_effect_of_exp(els)?;
        let boolean = self.bool_type;
        let ok = self.unify(test_t, boolean)?;
        self.require(ok, span, "test condition is not a boolean value")?;
        let ok = self.unify(then_t, else_t)?;
        self.require(ok, span, "test branches are incompatible")?;
        let ty = self.evaluate(then_t)?;
        let effect = self.p.arena.add(span, Fx::MaxEff(vec![test_e, then_e, else_e]));
        let effect = self.evaluate(effect)?;
        Ok((ty, effect))
    }

    fn type_of_begin(&mut self, id: FxId) -> R<TypeEffect> {
        let span = self.p.arena.span(id);
        let Fx::Begin(exps) = self.p.arena.get(id).clone() else { unreachable!() };
        if exps.is_empty() {
            return Err(FxError::user(span, "begin needs at least one expression"));
        }
        let mut effects = Vec::with_capacity(exps.len());
        let mut last = None;
        for e in &exps {
            let (t, ef) = self.type_effect_of_exp(*e)?;
            effects.push(ef);
            last = Some(t);
        }
        let effect = self.p.arena.add(span, Fx::MaxEff(effects));
        let effect = self.evaluate(effect)?;
        Ok((last.expect("non-empty"), effect))
    }

    fn type_of_open(&mut self, id: FxId) -> R<TypeEffect> {
        let span = self.p.arena.span(id);
        let Fx::Open(inner) = self.p.arena.get(id).clone() else { unreachable!() };
        let (poly_type, effect) = self.type_effect_of_exp(inner)?;
        let Fx::Poly { ids, kinds, body } = self.p.arena.get(poly_type).clone() else {
            return Err(FxError::user(span, "open should be applied to a polymorphic value"));
        };
        for (i, k) in ids.iter().zip(&kinds) {
            let fresh = self.fresh_unification(span, true, k.clone());
            self.store_set(*i, fresh);
        }
        let ty = self.evaluate(body)?;
        for i in &ids {
            self.store_remove(*i);
        }
        Ok((ty, effect))
    }

    /// `close` quantifies over every description variable free in the type but
    /// not in the environment — the explicit counterpart of `let`'s implicit
    /// generalisation.
    fn type_of_close(&mut self, id: FxId) -> R<TypeEffect> {
        let span = self.p.arena.span(id);
        let Fx::Close(inner) = self.p.arena.get(id).clone() else { unreachable!() };
        let (ty, effect) = self.type_effect_of_exp(inner)?;
        let env_dvars = free_dvars_of_free_vars(self.p.arena, id);
        let type_dvars = free_dvars_of_dexp(self.p.arena, ty);
        let poly_vars: Vec<FxId> = type_dvars
            .into_iter()
            .filter(|v| !env_dvars.iter().any(|e| self.p.arena.same_variable(*v, *e)))
            .collect();
        let mut kinds = Vec::with_capacity(poly_vars.len());
        for v in &poly_vars {
            kinds.push(self.kind_of_dexp(*v)?);
        }
        let new_ids: Vec<FxId> = poly_vars
            .iter()
            .map(|v| {
                let d = self.p.arena.var(*v).expect("a variable").clone();
                self.p.arena.identifier_variable(
                    span,
                    d.user_name,
                    d.name,
                    crate::ast::Domain::Description,
                )
            })
            .collect();
        for (v, n) in poly_vars.iter().zip(&new_ids) {
            self.store_set(*v, *n);
        }
        let body = self.evaluate(ty)?;
        let poly = self.p.arena.add(span, Fx::Poly { ids: new_ids, kinds, body });
        Ok((poly, effect))
    }

    fn type_of_the(&mut self, id: FxId) -> R<TypeEffect> {
        let span = self.p.arena.span(id);
        let Fx::The { ty, exp } = self.p.arena.get(id).clone() else { unreachable!() };
        let k = self.kind_of_dexp(ty)?;
        self.require(kind_eq(&k, &Kind::Type), span, "THE expects a type")?;
        let asserted = self.evaluate(ty)?;
        let (actual, effect) = self.type_effect_of_exp(exp)?;
        let ok = self.description_leq(actual, asserted)?;
        self.require(ok, span, "THE isn't passed a subtype")?;
        Ok((asserted, effect))
    }

    fn type_of_does(&mut self, id: FxId) -> R<TypeEffect> {
        let span = self.p.arena.span(id);
        let Fx::Does { effect: asserted_syntax, exp } = self.p.arena.get(id).clone() else {
            unreachable!()
        };
        let k = self.kind_of_dexp(asserted_syntax)?;
        self.require(kind_eq(&k, &Kind::Effect), span, "does expects an effect")?;
        let asserted = self.evaluate(asserted_syntax)?;
        let (ty, effect) = self.type_effect_of_exp(exp)?;
        let ok = self.description_leq(effect, asserted)?;
        self.require(ok, span, "does isn't passed a subeffect")?;
        Ok((ty, asserted))
    }

    fn type_of_sum(&mut self, id: FxId) -> R<TypeEffect> {
        let span = self.p.arena.span(id);
        let Fx::Sum { ty, tag, exp } = self.p.arena.get(id).clone() else { unreachable!() };
        let k = self.kind_of_dexp(ty)?;
        self.require(kind_eq(&k, &Kind::Type), span, "sum expects a type")?;
        let sumof = self.evaluate(ty)?;
        let (tags, types) = match self.p.arena.get(sumof).clone() {
            Fx::SumOf { tags, types } => (tags, types),
            _ => return Err(FxError::user(span, "sum expects a sumof type")),
        };
        let Some(i) = tags.iter().position(|t| *t == tag) else {
            return Err(FxError::user(span, "sumof doesn't have the sum tag"));
        };
        let (actual, effect) = self.type_effect_of_exp(exp)?;
        let ok = self.unify(actual, types[i])?;
        self.require(ok, span, "type is incompatible with sumof")?;
        let ty = self.evaluate(sumof)?;
        Ok((ty, effect))
    }

    fn type_of_product(&mut self, id: FxId) -> R<TypeEffect> {
        let span = self.p.arena.span(id);
        let Fx::Product { ty, exps } = self.p.arena.get(id).clone() else { unreachable!() };
        let k = self.kind_of_dexp(ty)?;
        self.require(kind_eq(&k, &Kind::Type), span, "product expects a type")?;
        let productof = self.evaluate(ty)?;
        let types = match self.p.arena.get(productof).clone() {
            Fx::ProductOf { types, .. } => types,
            _ => return Err(FxError::user(span, "product expects a productof type")),
        };
        self.require(
            exps.len() == types.len(),
            span,
            "incorrect number of expressions in productof",
        )?;
        let mut effects = Vec::with_capacity(exps.len());
        for (e, want) in exps.iter().zip(&types) {
            let (t, ef) = self.type_effect_of_exp(*e)?;
            effects.push(ef);
            let ok = self.unify(t, *want)?;
            self.require(ok, span, "types are incompatible with productof")?;
        }
        let ty = self.evaluate(productof)?;
        let effect = self.p.arena.add(span, Fx::MaxEff(effects));
        let effect = self.evaluate(effect)?;
        Ok((ty, effect))
    }

    fn type_of_tagcase(&mut self, id: FxId) -> R<TypeEffect> {
        let span = self.p.arena.span(id);
        let Fx::TagCase { ty, exp, tag, success, failure } = self.p.arena.get(id).clone() else {
            unreachable!()
        };
        let k = self.kind_of_dexp(ty)?;
        self.require(kind_eq(&k, &Kind::Type), span, "tagcase expects a type")?;
        let (sumof, effect) = self.type_effect_of_exp(exp)?;
        let declared = self.evaluate(ty)?;
        let ok = self.unify(sumof, declared)?;
        self.require(ok, span, "tagcase has incompatible type declaration")?;
        let (tags, types) = match self.p.arena.get(sumof).clone() {
            Fx::SumOf { tags, types } => (tags, types),
            _ => return Err(FxError::user(span, "tagcase expects a sumof value")),
        };
        let (success_type, success_effect) = self.type_effect_of_exp(success)?;
        let (failure_type, failure_effect) = self.type_effect_of_exp(failure)?;
        let Some(i) = tags.iter().position(|t| *t == tag) else {
            return Err(FxError::user(span, "tagcase tag is not in the sumof type"));
        };
        let match_type = types[i];
        let (se, s_types, s_body) = match self.p.arena.get(success_type).clone() {
            Fx::Subr { effect, types, body, .. } => (effect, types, body),
            _ => return Err(FxError::user(span, "success subroutine expected in tagcase")),
        };
        let (fe, f_types, f_body) = match self.p.arena.get(failure_type).clone() {
            Fx::Subr { effect, types, body, .. } => (effect, types, body),
            _ => return Err(FxError::user(span, "failure subroutine expected in tagcase")),
        };
        self.require(s_types.len() == 1, span, "success subroutine expects sum argument")?;
        self.require(f_types.len() == 1, span, "failure subroutine expects sum argument")?;
        let ok = self.unify(s_types[0], match_type)?;
        self.require(ok, span, "success subroutine is incompatible with tag")?;
        let ok = self.unify(f_types[0], sumof)?;
        self.require(ok, span, "failure subroutine is incompatible with sumof type")?;
        let ok = self.unify(s_body, f_body)?;
        self.require(ok, span, "subroutines don't return the same type in tagcase")?;
        let effect = self
            .p
            .arena
            .add(span, Fx::MaxEff(vec![effect, success_effect, failure_effect, se, fe]));
        let effect = self.evaluate(effect)?;
        Ok((s_body, effect))
    }

    fn type_of_extract(&mut self, id: FxId) -> R<TypeEffect> {
        let span = self.p.arena.span(id);
        let Fx::Extract { ty, exp, tag } = self.p.arena.get(id).clone() else { unreachable!() };
        let k = self.kind_of_dexp(ty)?;
        self.require(kind_eq(&k, &Kind::Type), span, "extract expects a type")?;
        let (productof, effect) = self.type_effect_of_exp(exp)?;
        let declared = self.evaluate(ty)?;
        let ok = self.unify(productof, declared)?;
        self.require(ok, span, "extract has incompatible type declaration")?;
        let (tags, types) = match self.p.arena.get(productof).clone() {
            Fx::ProductOf { tags, types } => (tags, types),
            _ => return Err(FxError::user(span, "extract expects a productof value")),
        };
        let Some(i) = tags.iter().position(|t| *t == tag) else {
            return Err(FxError::user(span, "tag isn't in productof type"));
        };
        Ok((types[i], effect))
    }

    // -------------------------------------------------------- application
    fn type_of_application(&mut self, id: FxId) -> R<TypeEffect> {
        let span = self.p.arena.span(id);
        let Fx::App { rator, rands } = self.p.arena.get(id).clone() else { unreachable!() };
        let (rator_type, rator_effect) = self.type_effect_of_exp(rator)?;
        let mut rand_types = Vec::with_capacity(rands.len());
        let mut rand_effects = Vec::with_capacity(rands.len());
        for r in &rands {
            let (t, e) = self.type_effect_of_exp(*r)?;
            rand_types.push(t);
            rand_effects.push(e);
        }
        // A polymorphic operator is instantiated implicitly.
        let subr_type = match self.p.arena.get(rator_type).clone() {
            Fx::Poly { ids, kinds, body } => {
                for (i, k) in ids.iter().zip(&kinds) {
                    let fresh = self.fresh_unification(span, true, k.clone());
                    self.store_set(*i, fresh);
                }
                let t = self.evaluate(body)?;
                for i in &ids {
                    self.store_remove(*i);
                }
                t
            }
            _ => rator_type,
        };
        let ids: Vec<FxId> = rands
            .iter()
            .map(|_| {
                let name = self.p.interner.intern("rand");
                let n = self.p.arena.fresh_name();
                let text = format!("rand-{n}");
                let sym = self.p.interner.intern(&text);
                let _ = name;
                self.p.arena.identifier_variable(span, sym, n, crate::ast::Domain::Value)
            })
            .collect();
        let effect_var = self.fresh_unification(span, false, Kind::Effect);
        let result_var = self.fresh_unification(span, false, Kind::Type);
        let expected = self.p.arena.add(
            span,
            Fx::Subr {
                effect: effect_var,
                ids: ids.clone(),
                types: rand_types.clone(),
                body: result_var,
            },
        );
        // The fresh parameter names are pre-bound to the actual argument
        // *expressions*, so a dependent result type can mention them.
        let ok = self.unify_with(subr_type, expected, &ids, &rands)?;
        self.require(ok, span, "incompatible subroutine in function position")?;
        let (subr_effect, subr_ids, subr_types, subr_body) =
            match self.p.arena.get(subr_type).clone() {
                Fx::Subr { effect, ids, types, body } => (effect, ids, types, body),
                _ => return Err(FxError::user(span, "incompatible subroutine in function position")),
            };
        self.require(subr_types.len() == rand_types.len(), span, "incorrect number of arguments")?;
        self.check_pure_dependent(subr_body, &subr_ids, &rand_effects)?;
        for (i, r) in subr_ids.iter().zip(&rands) {
            self.store_set(*i, *r);
        }
        let ty = self.evaluate(subr_body)?;
        for i in &subr_ids {
            self.store_remove(*i);
        }
        let mut all = vec![subr_effect, rator_effect];
        all.extend(rand_effects);
        let effect = self.p.arena.add(span, Fx::MaxEff(all));
        let effect = self.evaluate(effect)?;
        Ok((ty, effect))
    }

    /// A dependent result type may only mention arguments whose evaluation is
    /// pure — otherwise the `select` it builds would name an expression whose
    /// meaning depends on when it ran.
    fn check_pure_dependent(
        &mut self,
        body: FxId,
        ids: &[FxId],
        effects: &[FxId],
    ) -> R<()> {
        let span = self.p.arena.span(body);
        let frees = crate::free::free_vars_of_dexp(self.p.arena, body);
        for (i, e) in ids.iter().zip(effects) {
            let mentioned = frees.iter().any(|f| self.p.arena.same_variable(*i, *f));
            if !mentioned {
                continue;
            }
            let pure = self.pure(span);
            let ok = self.add_constraint(*e, pure)?;
            self.require(ok, span, "exported abstract type should use a pure expression")?;
        }
        Ok(())
    }

    // -------------------------------------------------------- generalisation
    /// Quantify over the unification variables a `let`-bound type is free in,
    /// unless the value restriction forbids it.
    pub fn generalize_over(
        &mut self,
        constraints: &[Constraint],
        exp: FxId,
        effect: FxId,
        ty: FxId,
    ) -> R<FxId> {
        let span = self.p.arena.span(ty);
        let gen_vars: Vec<FxId> = if self.algebraic && self.expansive(exp)? {
            Vec::new()
        } else {
            let env_dvars = free_dvars_of_free_vars(self.p.arena, exp);
            let exp_dvars: Vec<FxId> = free_dvars_of_exp(self.p.arena, exp)
                .into_iter()
                .filter(|v| self.p.arena.var(*v).is_some_and(|d| !d.is_unification()))
                .collect();
            let mut candidates = free_dvars_of_dexp(self.p.arena, ty);
            if self.algebraic {
                for c in constraints {
                    candidates.extend(free_dvars_of_dexp(self.p.arena, c.lhs));
                    candidates.extend(free_dvars_of_dexp(self.p.arena, c.rhs));
                }
            }
            let mut out: Vec<FxId> = Vec::new();
            for v in candidates {
                let is_unif = self.p.arena.var(v).is_some_and(|d| d.is_unification());
                if self.algebraic && !is_unif {
                    continue;
                }
                if env_dvars.iter().any(|e| self.p.arena.same_variable(v, *e))
                    || exp_dvars.iter().any(|e| self.p.arena.same_variable(v, *e))
                    || out.iter().any(|e| self.p.arena.same_variable(v, *e))
                {
                    continue;
                }
                if !self.algebraic {
                    let pure = self.pure(span);
                    if !self.unify(effect, pure)? {
                        continue;
                    }
                }
                out.push(v);
            }
            out
        };
        if gen_vars.is_empty() {
            return Ok(ty);
        }
        let mut kinds = Vec::with_capacity(gen_vars.len());
        for v in &gen_vars {
            kinds.push(self.kind_of_dexp(*v)?);
        }
        let scheme_vars: Vec<FxId> = gen_vars
            .iter()
            .map(|v| {
                let d = self.p.arena.var(*v).expect("a variable").clone();
                self.p.arena.identifier_variable(
                    span,
                    d.user_name,
                    d.name,
                    crate::ast::Domain::Description,
                )
            })
            .collect();
        for (v, s) in gen_vars.iter().zip(&scheme_vars) {
            self.store_set(*v, *s);
        }
        let body = self.evaluate(ty)?;
        let cs =
            if self.algebraic { self.evaluate_constraints(constraints)? } else { Vec::new() };
        let scheme = self.p.arena.add(
            span,
            Fx::PolyTilde { ids: scheme_vars, kinds, body, constraints: cs },
        );
        for v in &gen_vars {
            self.store_remove(*v);
        }
        Ok(scheme)
    }

    /// The value restriction. An expression that may allocate is expansive and
    /// its type is not generalised.
    pub fn expansive(&mut self, id: FxId) -> R<bool> {
        Ok(!self.not_expansive(id)?)
    }

    fn not_expansive(&mut self, id: FxId) -> R<bool> {
        Ok(match self.p.arena.get(id).clone() {
            Fx::Variable(_) | Fx::Lambda { .. } | Fx::PLambda { .. } => true,
            // An application may allocate, so it is expansive.
            Fx::App { .. } | Fx::Load { .. } => false,
            Fx::Begin(exps) => self.all_not_expansive(&exps)?,
            Fx::Extend { module, body, .. } | Fx::With { module, body, .. } => {
                self.not_expansive(module)? && self.not_expansive(body)?
            }
            Fx::Extract { exp, .. }
            | Fx::Open(exp)
            | Fx::Close(exp)
            | Fx::Proj { exp, .. }
            | Fx::Sum { exp, .. }
            | Fx::The { exp, .. } => self.not_expansive(exp)?,
            Fx::If { test, then, els } => self.all_not_expansive(&[test, then, els])?,
            Fx::Let { exps, body, .. } => {
                self.all_not_expansive(&exps)? && self.not_expansive(body)?
            }
            Fx::Module { define_exps, typed_exps, .. } => {
                let mut all = define_exps.clone();
                all.extend(typed_exps.iter().copied());
                self.all_not_expansive(&all)?
            }
            Fx::Product { exps, .. } => self.all_not_expansive(&exps)?,
            Fx::TagCase { exp, success, failure, .. } => {
                self.all_not_expansive(&[exp, success, failure])?
            }
            other => {
                return Err(FxError::fatal(
                    self.p.arena.span(id),
                    format!("unknown expression in expansive?: {}", crate::sugar::head_name(&other)),
                ));
            }
        })
    }

    fn all_not_expansive(&mut self, ids: &[FxId]) -> R<bool> {
        for i in ids {
            if !self.not_expansive(*i)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// `rename-moduleof`: give a module type fresh identities, so that two uses
    /// of the same signature do not share binders.
    pub fn rename_moduleof(&mut self, exp: FxId, ty: FxId) -> R<FxId> {
        let span = self.p.arena.span(ty);
        let Fx::ModuleOf { abs_ids, abs_kinds, desc_ids, desc_descs, val_ids, val_types } =
            self.p.arena.get(ty).clone()
        else {
            return Ok(ty);
        };
        if self.dont_alpha_rename_and_eval {
            return Ok(ty);
        }
        let mut originals = abs_ids.clone();
        originals.extend(desc_ids.iter().copied());
        originals.extend(val_ids.iter().copied());
        let renamed: Vec<FxId> = originals
            .iter()
            .map(|v| {
                let d = self.p.arena.var(*v).expect("a variable").clone();
                let fresh = self.p.arena.fresh_name();
                self.p.arena.add(
                    span,
                    Fx::Variable(crate::ast::VarData {
                        class: VarClass::Identifier,
                        user_name: d.user_name,
                        name: fresh,
                        domain: d.domain,
                        weak: false,
                        kind: None,
                        valuation: Vec::new(),
                    }),
                )
            })
            .collect();
        for (o, n) in originals.iter().zip(&renamed) {
            self.store_set(*o, *n);
        }
        let n_abs = abs_ids.len();
        let n_desc = desc_ids.len();
        let new_abs = renamed[..n_abs].to_vec();
        let new_desc = renamed[n_abs..n_abs + n_desc].to_vec();
        let new_val = renamed[n_abs + n_desc..].to_vec();
        let mut new_descs = Vec::with_capacity(desc_descs.len());
        for d in &desc_descs {
            new_descs.push(self.substitute_dexp(*d)?);
        }
        let mut new_types = Vec::with_capacity(val_types.len());
        for t in &val_types {
            new_types.push(self.substitute_dexp(*t)?);
        }
        let module = self.p.arena.add(
            span,
            Fx::ModuleOf {
                abs_ids: new_abs.clone(),
                abs_kinds,
                desc_ids: new_desc.clone(),
                desc_descs: new_descs,
                val_ids: new_val.clone(),
                val_types: new_types,
            },
        );
        // Carry the kinds and types across to the fresh identifiers.
        for (o, n) in originals.iter().zip(&renamed) {
            if let Some(entry) = self.tk_get(*o).cloned() {
                self.tk_set(*n, entry);
            }
        }
        self.p.arena.exp_info_mut(exp).ty = Some(module);
        Ok(module)
    }
}
