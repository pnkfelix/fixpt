//! Kind checking — `kind.scm`.
//!
//! Kinds classify descriptions the way types classify values: `type`, `effect`,
//! and `(dfunc k…)` for a description-level function. Every description is
//! kind-checked before it is believed, and the result is cached on the node.

use crate::ast::{Fx, FxId, Kind};
use crate::check::{kind_eq, Checker};
use crate::env::TkEntry;
use crate::error::{FxError, R};

impl Checker<'_> {
    pub fn kind_of_dexp(&mut self, id: FxId) -> R<Kind> {
        if let Some(k) = self.p.arena.info(id).kind.clone() {
            return Ok(k);
        }
        let k = self.kind_of_dexp_1(id)?;
        self.p.arena.info_mut(id).kind = Some(k.clone());
        Ok(k)
    }

    fn kind_of_dexp_1(&mut self, id: FxId) -> R<Kind> {
        let span = self.p.arena.span(id);
        match self.p.arena.get(id).clone() {
            Fx::Variable(v) => {
                if v.is_unification() {
                    return v.kind.clone().ok_or_else(|| {
                        FxError::fatal(span, "a unification variable without a kind")
                    });
                }
                let name = self.p.interner.name(v.user_name).to_string();
                let entry = self
                    .tk_env
                    .get(&v)
                    .ok_or_else(|| {
                        FxError::user(span, format!("unbound description variable {name}"))
                    })?
                    .clone();
                entry.as_kind().cloned().ok_or_else(|| {
                    FxError::user(span, format!("{name} is not a description"))
                })
            }

            Fx::DLambda { ids, kinds, body } => {
                for (i, k) in ids.iter().zip(&kinds) {
                    self.tk_set(*i, TkEntry::Kind(k.clone()));
                }
                let body_kind = self.kind_of_dexp(body)?;
                self.require(
                    kind_eq(&body_kind, &Kind::Type),
                    span,
                    "dlambda body should have a kind type",
                )?;
                Ok(Kind::DFunc(kinds))
            }

            Fx::Select { .. } => self.kind_of_select(id),

            Fx::MaxEff(effects) => {
                for e in &effects {
                    let k = self.kind_of_dexp(*e)?;
                    self.require(
                        kind_eq(&k, &Kind::Effect),
                        span,
                        "maxeff requires effect subexpressions",
                    )?;
                }
                Ok(Kind::Effect)
            }

            Fx::Subr { effect, ids, types, body } => {
                let ek = self.kind_of_dexp(effect)?;
                self.require(
                    kind_eq(&ek, &Kind::Effect),
                    span,
                    "subroutine latent effect is not an effect",
                )?;
                // A parameter is bound to its *normal form*, so that a later
                // parameter's type can mention it and still be evaluated.
                for (i, t) in ids.iter().zip(&types) {
                    let norm = self.value_of_dexp(*t)?;
                    self.tk_set(*i, TkEntry::Type(norm));
                }
                for t in &types {
                    let k = self.kind_of_dexp(*t)?;
                    self.require(
                        kind_eq(&k, &Kind::Type),
                        span,
                        "subroutine formal is not a type",
                    )?;
                }
                let bk = self.kind_of_dexp(body)?;
                self.require(
                    kind_eq(&bk, &Kind::Type),
                    span,
                    "subroutine body is not a type",
                )?;
                Ok(Kind::Type)
            }

            Fx::Poly { ids, kinds, body } => {
                for (i, k) in ids.iter().zip(&kinds) {
                    self.tk_set(*i, TkEntry::Kind(k.clone()));
                }
                let bk = self.kind_of_dexp(body)?;
                self.require(kind_eq(&bk, &Kind::Type), span, "poly body is not a type")?;
                Ok(Kind::Type)
            }

            Fx::ModuleOf { abs_ids, abs_kinds, val_types, .. } => {
                for (i, k) in abs_ids.iter().zip(&abs_kinds) {
                    self.tk_set(*i, TkEntry::Kind(k.clone()));
                }
                for t in &val_types {
                    let norm = self.evaluate(*t)?;
                    let k = self.kind_of_dexp(norm)?;
                    self.require(
                        kind_eq(&k, &Kind::Type),
                        span,
                        "value binding is not a type",
                    )?;
                }
                Ok(Kind::Type)
            }

            Fx::SumOf { types, .. } => {
                for t in &types {
                    let k = self.kind_of_dexp(*t)?;
                    self.require(
                        kind_eq(&k, &Kind::Type),
                        span,
                        "sumof component is not a type",
                    )?;
                }
                Ok(Kind::Type)
            }
            Fx::ProductOf { types, .. } => {
                for t in &types {
                    let k = self.kind_of_dexp(*t)?;
                    self.require(
                        kind_eq(&k, &Kind::Type),
                        span,
                        "productof component is not a type",
                    )?;
                }
                Ok(Kind::Type)
            }

            Fx::DApp { rator, rands } => {
                let rk = self.kind_of_dexp(rator)?;
                let Kind::DFunc(expected) = rk else {
                    return Err(FxError::user(span, "not a dfunc in operator position"));
                };
                self.require(
                    rands.len() == expected.len(),
                    span,
                    "incorrect number of arguments in dapplication",
                )?;
                for (r, want) in rands.iter().zip(&expected) {
                    let got = self.kind_of_dexp(*r)?;
                    self.require(
                        kind_eq(&got, want),
                        span,
                        "argument mismatch in dapplication",
                    )?;
                }
                Ok(Kind::Type)
            }

            _ => Err(FxError::user(span, "incorrect description expression")),
        }
    }

    /// `select`'s kind can only be found once the module expression has a
    /// type, so this is where kind checking reaches into type checking.
    fn kind_of_select(&mut self, id: FxId) -> R<Kind> {
        let span = self.p.arena.span(id);
        let Fx::Select { module, id: field } = self.p.arena.get(id).clone() else {
            unreachable!("called on a select")
        };
        let (mod_type, effect) = self.type_effect_of_exp(module)?;
        self.require(
            matches!(self.p.arena.get(mod_type), Fx::ModuleOf { .. }),
            span,
            "select requires a moduleof type",
        )?;
        let pure = self.pure(span);
        let ok = if self.algebraic {
            self.add_constraint(effect, pure)?
        } else {
            self.unify(effect, pure)?
        };
        self.require(ok, span, "select requires a pure expression")?;

        let renamed = self.rename_moduleof(module, mod_type)?;
        let (abs_ids, abs_kinds, desc_ids, desc_descs) = match self.p.arena.get(renamed) {
            Fx::ModuleOf { abs_ids, abs_kinds, desc_ids, desc_descs, .. } => {
                (abs_ids.clone(), abs_kinds.clone(), desc_ids.clone(), desc_descs.clone())
            }
            _ => unreachable!("checked above"),
        };
        for (i, k) in abs_ids.iter().zip(&abs_kinds) {
            if self.p.arena.var(*i).is_some_and(|v| v.user_name == field) {
                return Ok(k.clone());
            }
        }
        for (i, d) in desc_ids.iter().zip(&desc_descs) {
            if self.p.arena.var(*i).is_some_and(|v| v.user_name == field) {
                return self.kind_of_dexp(*d);
            }
        }
        Err(FxError::user(span, "unknown selector identifier"))
    }
}
