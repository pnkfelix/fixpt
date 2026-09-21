//! Description normal forms — `eval.scm` and `substitution.scm`.
//!
//! Descriptions are a little lambda calculus of their own, so comparing two of
//! them means reducing both first. [`Checker::evaluate`] performs beta *and*
//! eta reduction; [`Checker::substitute_dexp`] does the same walk without
//! reducing, for the places that need a description rebuilt under the current
//! store but not normalised.
//!
//! Two behaviours here matter far out of proportion to their size:
//!
//! * A one-element `maxeff` evaluates to that element, not to a singleton.
//!   That is why the goldens print `! read` and not `! (maxeff read)`.
//! * Eta reduction turns `(dlambda (x…) (f x…))` back into `f`, provided `f`
//!   does not itself mention the `x`s. Without it, descriptions that are equal
//!   would compare unequal and inference would fail in ways that look
//!   unrelated to the cause.

use crate::ast::{Fx, FxId};
use crate::check::Checker;
use crate::error::R;
use crate::free::free_dvars_of_dexp;

impl Checker {
    /// The cached normal form of a description.
    pub fn value_of_dexp(&mut self, id: FxId) -> R<FxId> {
        if let Some(n) = self.p.arena.info(id).norm {
            return Ok(n);
        }
        let n = self.evaluate(id)?;
        self.p.arena.info_mut(id).norm = Some(n);
        Ok(n)
    }

    pub fn evaluate(&mut self, id: FxId) -> R<FxId> {
        let span = self.p.arena.span(id);
        let new = match self.p.arena.get(id).clone() {
            // A variable evaluates to whatever the store says, or to itself.
            Fx::Variable(_) => self.store_get(id).unwrap_or_else(|| self.p.arena.find(id)),

            Fx::DLambda { ids, kinds, body } => {
                for i in &ids {
                    self.store_set(*i, *i);
                }
                let body = self.evaluate(body)?;
                let built = self.p.arena.add(span, Fx::DLambda { ids: ids.clone(), kinds, body });
                self.eta_reduce(built, &ids, body)?
            }

            Fx::Select { .. } => self.evaluate_select(id)?,

            Fx::MaxEff(effects) => {
                let mut evaluated = Vec::with_capacity(effects.len());
                for e in &effects {
                    evaluated.push(self.evaluate(*e)?);
                }
                // Flatten nested maxeffs and drop duplicates.
                //
                // Order is observable -- it is what the goldens print -- and
                // `utils.scm`'s `reduce` is a RIGHT fold, so the reference
                // walks the members backwards and prepends. On a duplicate
                // that keeps the *last* occurrence's position, not the first;
                // walking forwards and appending gives a different order for
                // exactly the expressions that mention an effect twice.
                let mut flat: Vec<FxId> = Vec::new();
                for e in evaluated.iter().rev() {
                    for member in self.p.arena.effect_list(*e).iter().rev() {
                        if !flat.iter().any(|x| self.description_eq(*member, *x)) {
                            flat.insert(0, *member);
                        }
                    }
                }
                match flat.len() {
                    // A singleton collapses; this is what makes `! read` print
                    // as `read`.
                    1 => flat[0],
                    _ => self.p.arena.add(span, Fx::MaxEff(flat)),
                }
            }

            Fx::Subr { effect, ids, types, body } => {
                let effect = self.evaluate(effect)?;
                let mut new_types = Vec::with_capacity(types.len());
                for t in &types {
                    new_types.push(self.evaluate(*t)?);
                }
                let body = self.evaluate(body)?;
                self.p.arena.add(span, Fx::Subr { effect, ids, types: new_types, body })
            }

            Fx::Poly { ids, kinds, body } => {
                for i in &ids {
                    self.store_set(*i, *i);
                }
                let body = self.evaluate(body)?;
                self.p.arena.add(span, Fx::Poly { ids, kinds, body })
            }

            Fx::PolyTilde { ids, kinds, body, constraints } => {
                for i in &ids {
                    self.store_set(*i, *i);
                }
                let body = self.evaluate(body)?;
                self.p.arena.add(span, Fx::PolyTilde { ids, kinds, body, constraints })
            }

            Fx::ModuleOf { abs_ids, abs_kinds, desc_ids, desc_descs, val_ids, val_types } => {
                for i in &abs_ids {
                    self.store_set(*i, *i);
                }
                let mut new_val_types = Vec::with_capacity(val_types.len());
                for t in &val_types {
                    new_val_types.push(self.evaluate(*t)?);
                }
                let built = self.p.arena.add(
                    span,
                    Fx::ModuleOf {
                        abs_ids,
                        abs_kinds,
                        desc_ids,
                        // Description members are deliberately not evaluated.
                        desc_descs,
                        val_ids: val_ids.clone(),
                        val_types: new_val_types.clone(),
                    },
                );
                // Each value identifier now carries its evaluated type, which
                // is how a `with` body sees it.
                for (v, t) in val_ids.iter().zip(&new_val_types) {
                    self.p.arena.exp_info_mut(*v).ty = Some(*t);
                }
                built
            }

            Fx::SumOf { tags, types } => {
                let mut new_types = Vec::with_capacity(types.len());
                for t in &types {
                    new_types.push(self.evaluate(*t)?);
                }
                self.p.arena.add(span, Fx::SumOf { tags, types: new_types })
            }
            Fx::ProductOf { tags, types } => {
                let mut new_types = Vec::with_capacity(types.len());
                for t in &types {
                    new_types.push(self.evaluate(*t)?);
                }
                self.p.arena.add(span, Fx::ProductOf { tags, types: new_types })
            }

            // Beta reduction.
            Fx::DApp { rator, rands } => {
                let rator = self.evaluate(rator)?;
                let mut new_rands = Vec::with_capacity(rands.len());
                for r in &rands {
                    new_rands.push(self.evaluate(*r)?);
                }
                match self.p.arena.get(rator).clone() {
                    Fx::DLambda { ids, body, .. } => {
                        for (i, r) in ids.iter().zip(&new_rands) {
                            self.store_set(*i, *r);
                        }
                        self.evaluate(body)?
                    }
                    _ => self.p.arena.add(span, Fx::DApp { rator, rands: new_rands }),
                }
            }

            _ => {
                let text = self.render_dexp(id);
                return Err(crate::error::FxError::fatal(
                    span,
                    format!("incorrect description expression in evaluate: {text}"),
                ));
            }
        };
        // `set-kind-of-description!`: the normal form inherits the source's
        // cached kind, whatever it is.
        let kind = self.p.arena.info(id).kind.clone();
        self.p.arena.info_mut(new).kind = kind;
        Ok(new)
    }

    /// `(dlambda (x…) (f x…))` reduces to `f`, when `f` does not mention the
    /// bound variables.
    fn eta_reduce(&mut self, built: FxId, ids: &[FxId], body: FxId) -> R<FxId> {
        let Fx::DApp { rator, rands } = self.p.arena.get(body).clone() else {
            return Ok(built);
        };
        if rands.len() != ids.len() {
            return Ok(built);
        }
        if !rands.iter().all(|r| self.p.arena.is_variable(*r)) {
            return Ok(built);
        }
        if !ids.iter().zip(&rands).all(|(i, r)| self.p.arena.same_variable(*i, *r)) {
            return Ok(built);
        }
        let frees = free_dvars_of_dexp(&mut self.p.arena, rator);
        let captures =
            ids.iter().any(|i| frees.iter().any(|f| self.p.arena.same_variable(*i, *f)));
        if captures { Ok(built) } else { Ok(rator) }
    }

    /// `(select m x)` where `x` names one of `m`'s *descriptions* reduces to
    /// that description; otherwise the select survives, over a substituted
    /// module expression.
    fn evaluate_select(&mut self, id: FxId) -> R<FxId> {
        let span = self.p.arena.span(id);
        let Fx::Select { module, id: field } = self.p.arena.get(id).clone() else {
            unreachable!("called on a select")
        };
        let mod_type = self.type_of_exp(module)?;
        let (abs_ids, desc_ids, desc_descs) = match self.p.arena.get(mod_type) {
            Fx::ModuleOf { abs_ids, desc_ids, desc_descs, .. } => {
                (abs_ids.clone(), desc_ids.clone(), desc_descs.clone())
            }
            _ => {
                return Err(crate::error::FxError::user(
                    span,
                    "select requires a moduleof type",
                ));
            }
        };
        let hit = desc_ids.iter().position(|d| {
            self.p.arena.var(*d).is_some_and(|v| v.user_name == field)
        });
        if let Some(i) = hit {
            // Abstractions stay reachable through the module while the
            // description is unfolded.
            for a in &abs_ids {
                let user = self.p.arena.var(*a).expect("a variable").user_name;
                let sel = self.p.arena.add(span, Fx::Select { module, id: user });
                self.store_set(*a, sel);
            }
            return self.evaluate(desc_descs[i]);
        }
        let new_mod = self.substitute(module)?;
        self.p.arena.exp_info_mut(new_mod).ty = Some(mod_type);
        Ok(self.p.arena.add(span, Fx::Select { module: new_mod, id: field }))
    }

    /// Rebuild a description under the current store, without reducing.
    pub fn substitute_dexp(&mut self, id: FxId) -> R<FxId> {
        let span = self.p.arena.span(id);
        let new = match self.p.arena.get(id).clone() {
            Fx::Variable(_) => self.store_get(id).unwrap_or_else(|| self.p.arena.find(id)),
            Fx::DLambda { ids, kinds, body } => {
                for i in &ids {
                    self.store_set(*i, *i);
                }
                let body = self.substitute_dexp(body)?;
                self.p.arena.add(span, Fx::DLambda { ids, kinds, body })
            }
            Fx::Select { module, id: field } => {
                let module = self.substitute(module)?;
                self.p.arena.add(span, Fx::Select { module, id: field })
            }
            Fx::MaxEff(effects) => {
                let mut new_effects = Vec::with_capacity(effects.len());
                for e in &effects {
                    new_effects.push(self.substitute_dexp(*e)?);
                }
                self.p.arena.add(span, Fx::MaxEff(new_effects))
            }
            Fx::Subr { effect, ids, types, body } => {
                let effect = self.substitute_dexp(effect)?;
                let mut new_types = Vec::with_capacity(types.len());
                for t in &types {
                    new_types.push(self.substitute_dexp(*t)?);
                }
                let body = self.substitute_dexp(body)?;
                self.p.arena.add(span, Fx::Subr { effect, ids, types: new_types, body })
            }
            Fx::Poly { ids, kinds, body } => {
                for i in &ids {
                    self.store_set(*i, *i);
                }
                let body = self.substitute_dexp(body)?;
                self.p.arena.add(span, Fx::Poly { ids, kinds, body })
            }
            Fx::PolyTilde { ids, kinds, body, constraints } => {
                for i in &ids {
                    self.store_set(*i, *i);
                }
                let body = self.substitute_dexp(body)?;
                self.p.arena.add(span, Fx::PolyTilde { ids, kinds, body, constraints })
            }
            Fx::ModuleOf { abs_ids, abs_kinds, desc_ids, desc_descs, val_ids, val_types } => {
                for i in &abs_ids {
                    self.store_set(*i, *i);
                }
                let mut new_descs = Vec::with_capacity(desc_descs.len());
                for d in &desc_descs {
                    new_descs.push(self.substitute_dexp(*d)?);
                }
                let mut new_types = Vec::with_capacity(val_types.len());
                for t in &val_types {
                    new_types.push(self.substitute_dexp(*t)?);
                }
                let built = self.p.arena.add(
                    span,
                    Fx::ModuleOf {
                        abs_ids,
                        abs_kinds,
                        desc_ids,
                        desc_descs: new_descs,
                        val_ids: val_ids.clone(),
                        val_types: new_types.clone(),
                    },
                );
                for (v, t) in val_ids.iter().zip(&new_types) {
                    self.p.arena.exp_info_mut(*v).ty = Some(*t);
                }
                built
            }
            Fx::SumOf { tags, types } => {
                let mut new_types = Vec::with_capacity(types.len());
                for t in &types {
                    new_types.push(self.substitute_dexp(*t)?);
                }
                self.p.arena.add(span, Fx::SumOf { tags, types: new_types })
            }
            Fx::ProductOf { tags, types } => {
                let mut new_types = Vec::with_capacity(types.len());
                for t in &types {
                    new_types.push(self.substitute_dexp(*t)?);
                }
                self.p.arena.add(span, Fx::ProductOf { tags, types: new_types })
            }
            Fx::DApp { rator, rands } => {
                let rator = self.substitute_dexp(rator)?;
                let mut new_rands = Vec::with_capacity(rands.len());
                for r in &rands {
                    new_rands.push(self.substitute_dexp(*r)?);
                }
                self.p.arena.add(span, Fx::DApp { rator, rands: new_rands })
            }
            _ => {
                let text = self.render_dexp(id);
                return Err(crate::error::FxError::fatal(
                    span,
                    format!("incorrect description in substitute: {text}"),
                ));
            }
        };
        let kind = self.p.arena.info(id).kind.clone();
        self.p.arena.info_mut(new).kind = kind;
        Ok(new)
    }

    /// Substitute value variables in an expression from the store.
    ///
    /// Needed when a type mentions a value variable that is escaping its
    /// scope — the case `with` and application both run into, and the reason
    /// the store holds value variables at all.
    pub fn substitute(&mut self, id: FxId) -> R<FxId> {
        let span = self.p.arena.span(id);
        Ok(match self.p.arena.get(id).clone() {
            Fx::Variable(_) => self.store_get(id).unwrap_or_else(|| self.p.arena.find(id)),
            Fx::Lambda { ids, types, user_types, body } => {
                let mut new_types = Vec::with_capacity(types.len());
                for t in &types {
                    new_types.push(self.evaluate(*t)?);
                }
                let body = self.substitute(body)?;
                self.p.arena.add(
                    span,
                    Fx::Lambda { ids, types: new_types, user_types, body },
                )
            }
            Fx::Let { ids, exps, body } => {
                let mut new_exps = Vec::with_capacity(exps.len());
                for e in &exps {
                    new_exps.push(self.substitute(*e)?);
                }
                let body = self.substitute(body)?;
                self.p.arena.add(span, Fx::Let { ids, exps: new_exps, body })
            }
            Fx::PLambda { ids, kinds, body } => {
                let body = self.substitute(body)?;
                self.p.arena.add(span, Fx::PLambda { ids, kinds, body })
            }
            Fx::Proj { exp, descs } => {
                let exp = self.substitute(exp)?;
                let mut new_descs = Vec::with_capacity(descs.len());
                for d in &descs {
                    new_descs.push(self.evaluate(*d)?);
                }
                self.p.arena.add(span, Fx::Proj { exp, descs: new_descs })
            }
            Fx::With { module, body, text } => {
                let module = self.substitute(module)?;
                let body = self.substitute(body)?;
                self.p.arena.add(span, Fx::With { module, body, text })
            }
            Fx::Extend { module, body, text } => {
                let module = self.substitute(module)?;
                let body = self.substitute(body)?;
                self.p.arena.add(span, Fx::Extend { module, body, text })
            }
            Fx::If { test, then, els } => {
                let test = self.substitute(test)?;
                let then = self.substitute(then)?;
                let els = self.substitute(els)?;
                self.p.arena.add(span, Fx::If { test, then, els })
            }
            Fx::Open(e) => {
                let e = self.substitute(e)?;
                self.p.arena.add(span, Fx::Open(e))
            }
            Fx::Close(e) => {
                let e = self.substitute(e)?;
                self.p.arena.add(span, Fx::Close(e))
            }
            Fx::Begin(exps) => {
                let mut new_exps = Vec::with_capacity(exps.len());
                for e in &exps {
                    new_exps.push(self.substitute(*e)?);
                }
                self.p.arena.add(span, Fx::Begin(new_exps))
            }
            Fx::App { rator, rands } => {
                let rator = self.substitute(rator)?;
                let mut new_rands = Vec::with_capacity(rands.len());
                for r in &rands {
                    new_rands.push(self.substitute(*r)?);
                }
                self.p.arena.add(span, Fx::App { rator, rands: new_rands })
            }
            Fx::The { ty, exp } => {
                let ty = self.evaluate(ty)?;
                let exp = self.substitute(exp)?;
                self.p.arena.add(span, Fx::The { ty, exp })
            }
            Fx::Does { effect, exp } => {
                let effect = self.evaluate(effect)?;
                let exp = self.substitute(exp)?;
                self.p.arena.add(span, Fx::Does { effect, exp })
            }
            Fx::Sum { ty, tag, exp } => {
                let ty = self.evaluate(ty)?;
                let exp = self.substitute(exp)?;
                self.p.arena.add(span, Fx::Sum { ty, tag, exp })
            }
            Fx::Product { ty, exps } => {
                let ty = self.evaluate(ty)?;
                let mut new_exps = Vec::with_capacity(exps.len());
                for e in &exps {
                    new_exps.push(self.substitute(*e)?);
                }
                self.p.arena.add(span, Fx::Product { ty, exps: new_exps })
            }
            Fx::TagCase { ty, exp, tag, success, failure } => {
                let ty = self.evaluate(ty)?;
                let exp = self.substitute(exp)?;
                let success = self.substitute(success)?;
                let failure = self.substitute(failure)?;
                self.p.arena.add(span, Fx::TagCase { ty, exp, tag, success, failure })
            }
            Fx::Extract { ty, exp, tag } => {
                let ty = self.evaluate(ty)?;
                let exp = self.substitute(exp)?;
                self.p.arena.add(span, Fx::Extract { ty, exp, tag })
            }
            // A module is rebuilt with its descriptions evaluated and its
            // bodies substituted — and **without** its source text, matching
            // `substitute-module`'s `unknown`. That is deliberate: the result
            // no longer corresponds to anything the user wrote, so printing it
            // verbatim would be a lie.
            Fx::Module {
                abs_ids,
                up_ids,
                down_ids,
                abs_kinds,
                abs_descs,
                desc_ids,
                desc_descs,
                define_ids,
                define_exps,
                typed_ids,
                typed_types,
                typed_exps,
                ..
            } => {
                let mut new_abs = Vec::with_capacity(abs_descs.len());
                for d in &abs_descs {
                    new_abs.push(self.evaluate(*d)?);
                }
                let mut new_desc = Vec::with_capacity(desc_descs.len());
                for d in &desc_descs {
                    new_desc.push(self.evaluate(*d)?);
                }
                let mut new_defs = Vec::with_capacity(define_exps.len());
                for e in &define_exps {
                    new_defs.push(self.substitute(*e)?);
                }
                let mut new_typed_types = Vec::with_capacity(typed_types.len());
                for t in &typed_types {
                    new_typed_types.push(self.evaluate(*t)?);
                }
                let mut new_typed = Vec::with_capacity(typed_exps.len());
                for e in &typed_exps {
                    new_typed.push(self.substitute(*e)?);
                }
                self.p.arena.add(
                    span,
                    Fx::Module {
                        abs_ids,
                        up_ids,
                        down_ids,
                        abs_kinds,
                        abs_descs: new_abs,
                        desc_ids,
                        desc_descs: new_desc,
                        define_ids,
                        define_exps: new_defs,
                        typed_ids,
                        typed_types: new_typed_types,
                        typed_exps: new_typed,
                        text: None,
                    },
                )
            }
            // `substitute-load` is the identity in the original.
            _ => self.p.arena.find(id),
        })
    }
}
