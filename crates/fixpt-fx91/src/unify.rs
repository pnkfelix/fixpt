//! Unification and description equality — `unify.scm`.
//!
//! One walk serves both, parameterised by what to do when it meets a
//! unification variable: bind it ([`Mode::Unify`]) or merely compare it
//! ([`Mode::VariableEq`]). `unify.scm` abstracts over exactly this, and sharing
//! the traversal is what keeps equality and unification from drifting apart.
//!
//! Binding is destructive — `forward!` — so a failed unification leaves
//! bindings behind. That is the reference's behaviour and the checker is built
//! around it; there is no backtracking anywhere in FX-91.
//!
//! Effects are special. Under algebraic reconstruction a `subr`'s latent
//! effects are not unified at all but *recorded as constraints* for the ACUI
//! solver, and only "safe" effect unifications — a unification variable against
//! a variable or against `pure` — are done directly. That split is what makes
//! effect inference tractable.

use crate::ast::{Fx, FxId, Kind};
use crate::check::{kind_eq, Checker};
use crate::error::R;
use crate::free::free_dvars_of_dexp;

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Mode {
    /// Bind unification variables.
    Unify,
    /// Compare only; `description=?`.
    VariableEq,
}

impl Checker<'_> {
    /// `unify?`
    pub fn unify(&mut self, a: FxId, b: FxId) -> R<bool> {
        self.unify_env_clear();
        self.unify_1(Mode::Unify, a, b)
    }

    /// `unify?` with an initial unify environment, for dependent subroutines.
    pub fn unify_with(&mut self, a: FxId, b: FxId, vars: &[FxId], vals: &[FxId]) -> R<bool> {
        self.unify_env_clear();
        self.unify_env_update(vars, vals);
        self.unify_1(Mode::Unify, a, b)
    }

    /// `description=-1?` — structural equality, no binding.
    pub fn description_eq(&mut self, a: FxId, b: FxId) -> bool {
        self.unify_1(Mode::VariableEq, a, b).unwrap_or(false)
    }

    fn unify_env_clear(&mut self) {
        self.unify_env.clear();
    }

    pub(crate) fn unify_env_pairs(&mut self, vars: &[FxId], vals: &[FxId]) {
        self.unify_env_update(vars, vals)
    }

    /// Two identifiers that the unify environment has paired up.
    pub(crate) fn same_after_unify_env(&self, a: FxId, b: FxId) -> bool {
        let va = self.unify_value(a);
        let vb = self.unify_value(b);
        self.p.arena.same_variable(va, vb)
    }

    pub(crate) fn match_moduleof_by_name(&mut self, a: FxId, b: FxId) {
        self.match_moduleof_names(a, b)
    }

    fn unify_env_update(&mut self, vars: &[FxId], vals: &[FxId]) {
        for (v, val) in vars.iter().zip(vals) {
            let resolved = self.unify_value(*val);
            if let Some(data) = self.p.arena.var(*v).cloned() {
                self.unify_env.set(&data, resolved);
            }
        }
    }

    fn unify_value(&self, id: FxId) -> FxId {
        match self.p.arena.var(id).and_then(|v| self.unify_env.get(v)) {
            Some(v) => *v,
            None => self.p.arena.find(id),
        }
    }

    pub(crate) fn unify_1(&mut self, mode: Mode, a: FxId, b: FxId) -> R<bool> {
        let a = self.p.arena.find(a);
        let b = self.p.arena.find(b);
        if a == b {
            return Ok(true);
        }
        let a_is_var = self.p.arena.is_variable(a);
        let b_is_var = self.p.arena.is_variable(b);
        if a_is_var {
            // Put a unification variable on the left where possible.
            let a_unif = self.p.arena.var(a).is_some_and(|v| v.is_unification());
            let b_unif = b_is_var && self.p.arena.var(b).is_some_and(|v| v.is_unification());
            return if a_unif || !b_unif {
                self.unify_variable(mode, a, b)
            } else {
                self.unify_variable(mode, b, a)
            };
        }
        if b_is_var {
            return self.unify_variable(mode, b, a);
        }
        if matches!(self.p.arena.get(a), Fx::PolyTilde { .. })
            || matches!(self.p.arena.get(b), Fx::PolyTilde { .. })
        {
            return Err(crate::error::FxError::fatal(
                self.p.arena.span(a),
                "trying to unify type schemes",
            ));
        }
        match self.p.arena.get(a).clone() {
            Fx::DLambda { .. } => self.unify_dlambda(mode, a, b),
            Fx::Select { .. } => self.unify_select(a, b),
            Fx::Subr { .. } => self.unify_subr(mode, a, b),
            Fx::Poly { .. } => self.unify_poly(mode, a, b),
            Fx::ModuleOf { .. } => self.unify_moduleof(mode, a, b),
            Fx::SumOf { .. } => self.unify_sum_or_product(mode, a, b, true),
            Fx::MaxEff(_) => self.unify_effect(mode, a, b),
            Fx::ProductOf { .. } => self.unify_sum_or_product(mode, a, b, false),
            Fx::DApp { .. } => self.unify_dapplication(mode, a, b),
            _ => Err(crate::error::FxError::fatal(
                self.p.arena.span(a),
                "unknown description in unify",
            )),
        }
    }

    fn unify_variable(&mut self, mode: Mode, a: FxId, b: FxId) -> R<bool> {
        if mode == Mode::VariableEq {
            return Ok(self.unify_variable_eq(a, b));
        }
        if kind_eq(&self.kind_of_dexp(a)?, &Kind::Effect) {
            return self.unify_effect(mode, a, b);
        }
        if self.p.arena.var(a).is_some_and(|v| v.is_unification()) {
            return self.unify_on_unification(a, b);
        }
        Ok(self.unify_variable_eq(a, b))
    }

    pub(crate) fn unify_variable_eq(&mut self, a: FxId, b: FxId) -> bool {
        if self.p.arena.is_variable(b) {
            let va = self.unify_value(a);
            let vb = self.unify_value(b);
            return self.p.arena.same_variable(va, vb);
        }
        if matches!(self.p.arena.get(b), Fx::Select { .. }) {
            // An abstraction may be reachable as a `select` on the module it
            // came from; `*select-env*` records that correspondence.
            let via = self.p.arena.var(a).and_then(|v| self.select_env.get(v)).copied();
            if let Some(sel) = via {
                return self.unify_select(sel, b).unwrap_or(false);
            }
        }
        false
    }

    /// Bind `unif` to `dexp`, with the occurs check.
    fn unify_on_unification(&mut self, unif: FxId, dexp: FxId) -> R<bool> {
        let unif_weak = self.p.arena.var(unif).is_some_and(|v| v.weak);
        let dexp_is_unif = self.p.arena.var(dexp).is_some_and(|v| v.is_unification());
        let dexp_weak = self.p.arena.var(dexp).is_some_and(|v| v.weak);
        // Prefer binding the weak one, so a strong variable survives.
        if dexp_is_unif && !dexp_weak && unif_weak {
            return self.unify_on_unification(dexp, unif);
        }
        let frees = free_dvars_of_dexp(self.p.arena, dexp);
        let occurs = frees.iter().any(|f| self.p.arena.same_variable(unif, *f));
        if !occurs {
            return Ok(self.normal_unify(unif, dexp));
        }
        if self.p.arena.is_variable(dexp) {
            if self.p.arena.same_variable(unif, dexp) {
                return Ok(true);
            }
            return Ok(self.normal_unify(unif, dexp));
        }
        Ok(false)
    }

    fn normal_unify(&mut self, u: FxId, d: FxId) -> bool {
        let weak = self.p.arena.var(u).is_some_and(|v| v.weak);
        if weak && !self.inferable(d) {
            return false;
        }
        self.p.arena.forward(u, d)
    }

    /// `inferable?`. Under the reference's default settings
    /// (`*forget-about-inferability*` is `#t`) this is unconditionally true —
    /// the D_i restriction from the report is switched off — so the predicate
    /// exists to make that visible rather than to be silently absent.
    pub fn inferable(&mut self, _d: FxId) -> bool {
        if self.forget_inferability {
            return true;
        }
        true
    }

    /// Effects. Under algebraic reconstruction only the safe cases unify
    /// directly; everything else becomes a constraint elsewhere.
    fn unify_effect(&mut self, mode: Mode, a: FxId, b: FxId) -> R<bool> {
        if mode == Mode::VariableEq {
            let fa = free_dvars_of_dexp(self.p.arena, a);
            let fb = free_dvars_of_dexp(self.p.arena, b);
            let same = fa.iter().all(|x| fb.iter().any(|y| self.p.arena.same_variable(*x, *y)))
                && fb.iter().all(|y| fa.iter().any(|x| self.p.arena.same_variable(*x, *y)));
            return Ok(same);
        }
        let a_unif = self.p.arena.var(a).is_some_and(|v| v.is_unification());
        let b_unif = self.p.arena.var(b).is_some_and(|v| v.is_unification());
        let a_simple = self.p.arena.is_pure(a) || self.p.arena.is_variable(a);
        let b_simple = self.p.arena.is_pure(b) || self.p.arena.is_variable(b);
        if a_unif && b_simple {
            return self.unify_on_unification(a, b);
        }
        // The original reads `(variable? exp1)` here — a typo for `dexp1`,
        // which the Racket port corrects. Corrected the same way.
        if b_unif && a_simple {
            return self.unify_on_unification(b, a);
        }
        Ok(false)
    }

    fn unify_dlambda(&mut self, mode: Mode, a: FxId, b: FxId) -> R<bool> {
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
        self.unify_env_update(&ids1, &ids2);
        self.unify_1(mode, body1, body2)
    }

    fn unify_select(&mut self, a: FxId, b: FxId) -> R<bool> {
        let (m1, f1) = match self.p.arena.get(a).clone() {
            Fx::Select { module, id } => (module, id),
            _ => return Ok(false),
        };
        let (m2, f2) = match self.p.arena.get(b).clone() {
            Fx::Select { module, id } => (module, id),
            _ => return Ok(false),
        };
        Ok(f1 == f2 && self.expression_eq(m1, m2))
    }

    fn unify_subr(&mut self, mode: Mode, a: FxId, b: FxId) -> R<bool> {
        let (e1, ids1, types1, body1) = match self.p.arena.get(a).clone() {
            Fx::Subr { effect, ids, types, body } => (effect, ids, types, body),
            _ => return Ok(false),
        };
        let (e2, ids2, types2, body2) = match self.p.arena.get(b).clone() {
            Fx::Subr { effect, ids, types, body } => (effect, ids, types, body),
            _ => return Ok(false),
        };
        if ids1.len() != ids2.len() {
            return Ok(false);
        }
        self.unify_env_update(&ids1, &ids2);
        for (t1, t2) in types1.iter().zip(&types2) {
            if !self.unify_1(mode, *t1, *t2)? {
                return Ok(false);
            }
        }
        if !self.unify_1(mode, body1, body2)? {
            return Ok(false);
        }
        // Latent effects become a constraint rather than a unification.
        if self.algebraic && mode == Mode::Unify {
            self.add_constraint(e1, e2)
        } else {
            self.unify_1(mode, e1, e2)
        }
    }

    /// Reproduces a real bug in the 1991 source, deliberately.
    ///
    /// `unify.scm`'s `unify-poly?` compares `(poly-body dexp1)` with
    /// `(poly-body dexp1)` — the *same* body twice — so two `poly` types with
    /// matching arity and kinds always unify, whatever their bodies say. The
    /// Racket port preserves it, and since the reference is what defines which
    /// programs FX-91 accepts, matching it is what makes the 182-case corpus
    /// mean anything. Fixing it here would produce disagreements
    /// indistinguishable from our own mistakes.
    ///
    /// Recorded in `docs/divergences.md`; `unify_poly_reproduces_the_1991_bug`
    /// pins the behaviour and states what the intended comparison was.
    fn unify_poly(&mut self, mode: Mode, a: FxId, b: FxId) -> R<bool> {
        let (ids1, kinds1, body1) = match self.p.arena.get(a).clone() {
            Fx::Poly { ids, kinds, body } => (ids, kinds, body),
            _ => return Ok(false),
        };
        let (ids2, kinds2, _body2) = match self.p.arena.get(b).clone() {
            Fx::Poly { ids, kinds, body } => (ids, kinds, body),
            _ => return Ok(false),
        };
        if ids1.len() != ids2.len() || !kinds1.iter().zip(&kinds2).all(|(x, y)| kind_eq(x, y)) {
            return Ok(false);
        }
        let constants: Vec<FxId> =
            kinds1.iter().map(|k| self.fresh_description_constant(k.clone())).collect();
        self.unify_env_update(&ids1, &constants);
        self.unify_env_update(&ids2, &constants);
        if self.algebraic {
            for (i, c) in ids1.iter().zip(&constants) {
                self.store_set(*i, *c);
            }
            for (i, c) in ids2.iter().zip(&constants) {
                self.store_set(*i, *c);
            }
        }
        let left = if self.algebraic { self.evaluate(body1)? } else { body1 };
        // …and here is the bug: `left` against itself.
        let right = left;
        self.unify_1(mode, left, right)
    }

    fn unify_moduleof(&mut self, mode: Mode, a: FxId, b: FxId) -> R<bool> {
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
        // Identifiers are matched by *user* name across the two signatures, so
        // a submodule's declaration order need not match.
        self.match_moduleof_names(a, b);
        if abs1.len() != abs2.len() || val1.len() != val2.len() {
            return Ok(false);
        }
        for (i2, k2) in abs2.iter().zip(&kinds2) {
            let found = abs1.iter().zip(&kinds1).any(|(i1, k1)| {
                self.p.arena.same_variable(self.unify_value(*i1), self.unify_value(*i2))
                    && kind_eq(k1, k2)
            });
            if !found {
                return Ok(false);
            }
        }
        for (i2, t2) in val2.iter().zip(&types2) {
            let mut ok = false;
            for (i1, t1) in val1.iter().zip(&types1) {
                let same = self
                    .p
                    .arena
                    .same_variable(self.unify_value(*i1), self.unify_value(*i2));
                if same && self.unify_1(mode, *t1, *t2)? {
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

    /// `update-moduleof-tk-env-unify`: pair up identifiers of the two
    /// signatures by user name. Order matters — the first may be a submodule of
    /// the second.
    fn match_moduleof_names(&mut self, a: FxId, b: FxId) {
        let ids1 = self.moduleof_ids(a);
        let ids2 = self.moduleof_ids(b);
        for i2 in &ids2 {
            let Some(name2) = self.p.arena.var(*i2).map(|v| v.user_name) else { continue };
            for i1 in &ids1 {
                if self.p.arena.var(*i1).is_some_and(|v| v.user_name == name2) {
                    self.unify_env_update(&[*i1], &[*i2]);
                }
            }
        }
    }

    fn moduleof_ids(&self, id: FxId) -> Vec<FxId> {
        match self.p.arena.get(id) {
            Fx::ModuleOf { abs_ids, desc_ids, val_ids, .. } => {
                let mut out = abs_ids.clone();
                out.extend(desc_ids.iter().copied());
                out.extend(val_ids.iter().copied());
                out
            }
            _ => Vec::new(),
        }
    }

    fn unify_sum_or_product(&mut self, mode: Mode, a: FxId, b: FxId, is_sum: bool) -> R<bool> {
        let get = |arena: &crate::ast::Arena, id: FxId| match arena.get(id) {
            Fx::SumOf { tags, types } if is_sum => Some((tags.clone(), types.clone())),
            Fx::ProductOf { tags, types } if !is_sum => Some((tags.clone(), types.clone())),
            _ => None,
        };
        let Some((tags1, types1)) = get(self.p.arena, a) else { return Ok(false) };
        let Some((tags2, types2)) = get(self.p.arena, b) else { return Ok(false) };
        if tags1.len() != tags2.len() {
            return Ok(false);
        }
        // A productof additionally requires the tags in the same order.
        if !is_sum && !tags1.iter().zip(&tags2).all(|(x, y)| x == y) {
            return Ok(false);
        }
        for (t2, ty2) in tags2.iter().zip(&types2) {
            let mut ok = false;
            for (t1, ty1) in tags1.iter().zip(&types1) {
                if t1 == t2 && self.unify_1(mode, *ty1, *ty2)? {
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

    fn unify_dapplication(&mut self, mode: Mode, a: FxId, b: FxId) -> R<bool> {
        let (r1, rands1) = match self.p.arena.get(a).clone() {
            Fx::DApp { rator, rands } => (rator, rands),
            _ => return Ok(false),
        };
        let (r2, rands2) = match self.p.arena.get(b).clone() {
            Fx::DApp { rator, rands } => (rator, rands),
            _ => return Ok(false),
        };
        if rands1.len() != rands2.len() {
            return Ok(false);
        }
        if !self.unify_1(mode, r1, r2)? {
            return Ok(false);
        }
        for (x, y) in rands1.iter().zip(&rands2) {
            if !self.unify_1(mode, *x, *y)? {
                return Ok(false);
            }
        }
        Ok(self.p.arena.forward(a, b))
    }

    fn fresh_description_constant(&mut self, kind: Kind) -> FxId {
        let name = self.p.arena.fresh_name();
        let text = format!("C{name}");
        let sym = self.p.interner.intern(&text);
        let span = fixpt_read::Span::new(fixpt_read::FileId(0), 0, 0);
        let id = self.p.arena.identifier_variable(
            span,
            sym,
            name,
            crate::ast::Domain::Description,
        );
        self.p.arena.info_mut(id).kind = Some(kind);
        id
    }

    /// `expression=-1?`: structural equality of value expressions.
    ///
    /// Needed because a *type* can contain an expression — `(select m t)` and
    /// `(with m x)` both do — so deciding whether two types are the same can
    /// require deciding whether two expressions are.
    ///
    /// Three self-comparisons in the original are preserved rather than
    /// repaired, for the reason given on [`Checker::unify_poly`]: the reference
    /// is what defines acceptance. They are pinned by tests and listed in
    /// `docs/divergences.md`.
    pub fn expression_eq(&mut self, a: FxId, b: FxId) -> bool {
        let a = self.unify_value(self.p.arena.find(a));
        let b = self.unify_value(self.p.arena.find(b));
        if a == b {
            return true;
        }
        match self.p.arena.get(a).clone() {
            Fx::Variable(_) => self.unify_variable_eq(a, b),
            Fx::Lambda { ids: i1, types: t1, user_types: u1, body: b1 } => {
                let Fx::Lambda { ids: i2, types: t2, user_types: u2, body: b2 } =
                    self.p.arena.get(b).clone()
                else {
                    return false;
                };
                i1.len() == i2.len()
                    && u1 == u2
                    && self.rename_in_unify_env(&i1, &i2)
                    && i1.iter().zip(&i2).all(|(x, y)| self.expression_eq(*x, *y))
                    && t1.iter().zip(&t2).all(|(x, y)| self.description_eq(*x, *y))
                    && self.expression_eq(b1, b2)
            }
            Fx::PLambda { ids: i1, kinds: k1, body: b1 } => {
                // The original tests `dexp2` here, an unbound variable; the
                // Racket port corrects it to `exp2`, and so does this.
                let Fx::PLambda { ids: i2, kinds: k2, body: b2 } = self.p.arena.get(b).clone()
                else {
                    return false;
                };
                i1.len() == i2.len()
                    && self.rename_in_unify_env(&i1, &i2)
                    && i1.iter().zip(&i2).all(|(x, y)| self.description_eq(*x, *y))
                    && k1.iter().zip(&k2).all(|(x, y)| kind_eq(x, y))
                    && self.expression_eq(b1, b2)
            }
            Fx::Proj { exp: e1, descs: d1 } => {
                // Same corrected typo as `PLambda`.
                let Fx::Proj { exp: e2, descs: d2 } = self.p.arena.get(b).clone() else {
                    return false;
                };
                self.expression_eq(e1, e2)
                    && d1.len() == d2.len()
                    && d1.iter().zip(&d2).all(|(x, y)| self.description_eq(*x, *y))
            }
            Fx::Module { .. } => self.module_eq(a, b),
            Fx::With { module: m1, body: b1, .. } => {
                let Fx::With { module: m2, body: b2, .. } = self.p.arena.get(b).clone() else {
                    return false;
                };
                self.expression_eq(m1, m2) && self.expression_eq(b1, b2)
            }
            Fx::Extend { module: m1, body: b1, .. } => {
                let Fx::Extend { module: m2, body: b2, .. } = self.p.arena.get(b).clone() else {
                    return false;
                };
                self.expression_eq(m1, m2) && self.expression_eq(b1, b2)
            }
            Fx::If { test: t1, then: y1, els: e1 } => {
                let Fx::If { test: t2, then: y2, els: e2 } = self.p.arena.get(b).clone() else {
                    return false;
                };
                self.expression_eq(t1, t2)
                    && self.expression_eq(y1, y2)
                    && self.expression_eq(e1, e2)
            }
            Fx::Open(x) => match self.p.arena.get(b).clone() {
                Fx::Open(y) => self.expression_eq(x, y),
                _ => false,
            },
            Fx::Close(x) => match self.p.arena.get(b).clone() {
                Fx::Close(y) => self.expression_eq(x, y),
                _ => false,
            },
            // `begin=?` uses `map`, not `every?`, so its result is a non-empty
            // list — always true in Scheme. Preserved: it compares nothing.
            Fx::Begin(_) => matches!(self.p.arena.get(b), Fx::Begin(_)),
            Fx::Load { path: p1, .. } => match self.p.arena.get(b).clone() {
                Fx::Load { path: p2, .. } => p1 == p2,
                _ => false,
            },
            Fx::The { exp: x, .. } => match self.p.arena.get(b).clone() {
                Fx::The { exp: y, .. } => self.expression_eq(x, y),
                _ => false,
            },
            Fx::Does { exp: x, .. } => match self.p.arena.get(b).clone() {
                Fx::Does { exp: y, .. } => self.expression_eq(x, y),
                _ => false,
            },
            // The dispatcher calls `sum=?`/`product=?` with `(exp1 exp1)`, so
            // both compare a node with itself and succeed on shape alone.
            // Preserved.
            Fx::Sum { .. } => matches!(self.p.arena.get(a), Fx::Sum { .. }),
            // …and `product=?` additionally tests `(sum? exp2)` rather than
            // `product?`. With the self-comparison above this is unreachable
            // in practice; kept faithful anyway.
            Fx::Product { .. } => matches!(self.p.arena.get(a), Fx::Sum { .. }),
            Fx::TagCase { ty: ty1, exp: e1, tag: g1, success: s1, failure: f1 } => {
                let Fx::TagCase { ty: ty2, exp: e2, tag: g2, success: s2, failure: f2 } =
                    self.p.arena.get(b).clone()
                else {
                    return false;
                };
                self.description_eq(ty1, ty2)
                    && self.expression_eq(e1, e2)
                    && g1 == g2
                    && self.expression_eq(s1, s2)
                    && self.expression_eq(f1, f2)
            }
            Fx::Extract { ty: ty1, exp: e1, tag: g1 } => {
                let Fx::Extract { ty: ty2, exp: e2, tag: g2 } = self.p.arena.get(b).clone()
                else {
                    return false;
                };
                self.description_eq(ty1, ty2) && self.expression_eq(e1, e2) && g1 == g2
            }
            Fx::App { rator: r1, rands: a1 } => {
                let Fx::App { rator: r2, rands: a2 } = self.p.arena.get(b).clone() else {
                    return false;
                };
                self.expression_eq(r1, r2)
                    && a1.len() == a2.len()
                    && a1.iter().zip(&a2).all(|(x, y)| self.expression_eq(*x, *y))
            }
            _ => false,
        }
    }

    /// Pair up two binder lists, but only if they were written with the same
    /// names — `rename-in-unify-env!`.
    fn rename_in_unify_env(&mut self, ids1: &[FxId], ids2: &[FxId]) -> bool {
        let same = ids1.iter().zip(ids2).all(|(x, y)| {
            self.p.arena.var(*x).map(|v| v.user_name)
                == self.p.arena.var(*y).map(|v| v.user_name)
        });
        if !same {
            return false;
        }
        self.unify_env_update(ids1, ids2);
        true
    }

    fn module_eq(&mut self, a: FxId, b: FxId) -> bool {
        let Fx::Module {
            abs_ids: a1,
            abs_kinds: ak1,
            abs_descs: ad1,
            up_ids: u1,
            down_ids: d1,
            desc_ids: dsi1,
            desc_descs: dsd1,
            define_ids: vi1,
            define_exps: ve1,
            typed_ids: ti1,
            typed_types: tt1,
            typed_exps: te1,
            ..
        } = self.p.arena.get(a).clone()
        else {
            return false;
        };
        let Fx::Module {
            abs_ids: a2,
            abs_kinds: ak2,
            abs_descs: ad2,
            up_ids: u2,
            down_ids: d2,
            desc_ids: dsi2,
            desc_descs: dsd2,
            define_ids: vi2,
            define_exps: ve2,
            typed_ids: ti2,
            typed_types: tt2,
            typed_exps: te2,
            ..
        } = self.p.arena.get(b).clone()
        else {
            return false;
        };
        if a1.len() != a2.len() || dsi1.len() != dsi2.len() {
            return false;
        }
        if vi1.len() != vi2.len() || ti1.len() != ti2.len() {
            return false;
        }
        if !self.rename_in_unify_env(&a1, &a2) {
            return false;
        }
        // Members are matched by identifier rather than by position, so
        // declaration order need not agree.
        if !self.paired(&a2, &ak2, &a1, &ak1, |_me, x, y| kind_eq(x, y)) {
            return false;
        }
        if !self.paired_ids(&a2, &ad2, &a1, &ad1, |me, x, y| me.description_eq(x, y)) {
            return false;
        }
        if !self.rename_in_unify_env(&dsi1, &dsi2) {
            return false;
        }
        if !self.paired_ids(&dsi2, &dsd2, &dsi1, &dsd1, |me, x, y| me.description_eq(x, y)) {
            return false;
        }
        if !self.rename_in_unify_env(&u1, &u2)
            || !self.rename_in_unify_env(&d1, &d2)
            || !self.rename_in_unify_env(&vi1, &vi2)
            || !self.rename_in_unify_env(&ti1, &ti2)
        {
            return false;
        }
        self.paired_ids(&vi2, &ve2, &vi1, &ve1, |me, x, y| me.expression_eq(x, y))
            && self.paired_ids(&ti2, &te2, &ti1, &te1, |me, x, y| me.expression_eq(x, y))
            && self.paired_ids(&ti2, &tt2, &ti1, &tt1, |me, x, y| me.description_eq(x, y))
    }

    /// `(match-and-test unify-variable=? test)`: for each `(id, value)` on the
    /// right, find a left entry whose identifier matches and whose value passes.
    fn paired_ids<F>(
        &mut self,
        ids1: &[FxId],
        vals1: &[FxId],
        ids2: &[FxId],
        vals2: &[FxId],
        mut test: F,
    ) -> bool
    where
        F: FnMut(&mut Self, FxId, FxId) -> bool,
    {
        for (i2, v2) in ids2.iter().zip(vals2) {
            let mut ok = false;
            for (i1, v1) in ids1.iter().zip(vals1) {
                if self.unify_variable_eq(*i1, *i2) && test(self, *v1, *v2) {
                    ok = true;
                    break;
                }
            }
            if !ok {
                return false;
            }
        }
        true
    }

    fn paired<F>(
        &mut self,
        ids1: &[FxId],
        vals1: &[Kind],
        ids2: &[FxId],
        vals2: &[Kind],
        mut test: F,
    ) -> bool
    where
        F: FnMut(&mut Self, &Kind, &Kind) -> bool,
    {
        for (i2, v2) in ids2.iter().zip(vals2) {
            let mut ok = false;
            for (i1, v1) in ids1.iter().zip(vals1) {
                if self.unify_variable_eq(*i1, *i2) && test(self, v1, v2) {
                    ok = true;
                    break;
                }
            }
            if !ok {
                return false;
            }
        }
        true
    }
}
