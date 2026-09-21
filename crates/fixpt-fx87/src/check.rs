//! The type and effect checker — `desc-of-exp`.
//!
//! Every rule returns a *description*: a type paired with the effect of
//! producing it. That pairing is the language's whole idea, and it shows most
//! clearly in `lambda`, where the body's effect does not become the lambda's —
//! it becomes *latent* in the arrow, and the lambda itself is `pure`.
//!
//! # `purify`, and why `@=` costs nothing
//!
//! The immutable region cannot be written, so nothing done to it is
//! observable. `purify` turns any `read`, `write` or `alloc` of `@=` into
//! `pure`, and rejects a write to it outright. That single rule is why
//! `(lambda ((x int)) x)` is pure despite `desc-of-variable` charging a
//! `(read r)` for every variable mention, and why `(new 3)` — which really does
//! allocate — is pure too.
//!
//! # Masking
//!
//! The other half is [`mask`](crate::mask): an effect on a region that cannot
//! escape is dropped. `purify` handles the region that is immutable by nature;
//! masking handles the region that happens to be private.

use crate::ast::{Arena, Binder, Binding, Desc, DescId, Exp, ExpId, Kind, Param};
use crate::env::{TkEnv, ValueBinding};
use crate::error::{FxError, R};
use crate::eval::{self, DStore};
use crate::mask::erase_effect;
use crate::parse::Parser;
use crate::subtype::Rel;
use crate::unparse::unparse;
use fixpt_read::{Span, Sym};
use std::collections::HashSet;

/// A type and the effect of producing it.
#[derive(Copy, Clone, Debug)]
pub struct Desc2 {
    pub ty: DescId,
    pub effect: DescId,
}

pub struct Checker {
    pub p: Parser,
    pub env: TkEnv,
    pub store: DStore,
    immutable: Sym,
    ref_name: Sym,
}

impl Checker {
    pub fn new() -> R<Checker> {
        let mut p = Parser::new();
        let std = crate::standard::load(&mut p)?;
        let immutable = p.syms.region_eq;
        let ref_name = p.syms.ref_;
        Ok(Checker { p, env: std.env, store: std.store, immutable, ref_name })
    }

    fn rel(&self) -> Rel<'_> {
        Rel::new(&self.p.arena, self.immutable, self.ref_name)
    }

    fn arena(&mut self) -> &mut Arena {
        &mut self.p.arena
    }

    // ------------------------------------------------------------ effects
    /// Build `(read r)`, `(write r)` or `(alloc r)`, collapsing the immutable
    /// region to `pure` — `purify` in the reference.
    fn effect_on(&mut self, span: Span, kind: EffectKind, region: DescId) -> R<DescId> {
        let members: Vec<DescId> = match self.p.arena.get(region) {
            Desc::RUnion(parts) => parts.clone(),
            _ => vec![region],
        };
        let mutable: Vec<DescId> =
            members.into_iter().filter(|r| !self.is_immutable(*r)).collect();
        if mutable.is_empty() {
            return Ok(self.arena().desc(Desc::Pure));
        }
        if kind == EffectKind::Write && mutable.iter().any(|r| self.is_immutable(*r)) {
            return Err(FxError::syntax(span, "WRITE is prohibited on the immutable region"));
        }
        let r = if mutable.len() == 1 {
            mutable[0]
        } else {
            self.arena().desc(Desc::RUnion(mutable))
        };
        Ok(self.arena().desc(match kind {
            EffectKind::Read => Desc::Read(r),
            EffectKind::Write => Desc::Write(r),
            EffectKind::Alloc => Desc::Alloc(r),
        }))
    }

    /// Apply `purify` throughout an effect that arrived by substitution.
    ///
    /// `effect_on` purifies the effects this checker *builds*, but a
    /// subroutine's latent effect arrives already built and is only made
    /// concrete when its region binder is instantiated — `new`'s `(alloc r)`
    /// becomes `(alloc @=)` at the moment of implicit projection. The
    /// reference reaches this through `eval-eexp`, which purifies every time;
    /// here it is a separate walk applied wherever a substituted effect
    /// surfaces.
    pub fn purify_effect(&mut self, effect: DescId) -> R<DescId> {
        let span = Span::new(fixpt_read::FileId(0), 0, 0);
        match self.p.arena.get(effect).clone() {
            Desc::Read(r) => self.effect_on(span, EffectKind::Read, r),
            Desc::Write(r) => self.effect_on(span, EffectKind::Write, r),
            Desc::Alloc(r) => self.effect_on(span, EffectKind::Alloc, r),
            Desc::MaxEff(parts) => {
                let mut out = Vec::with_capacity(parts.len());
                for p in parts {
                    out.push(self.purify_effect(p)?);
                }
                Ok(self.arena().maxeff(out))
            }
            _ => Ok(effect),
        }
    }

    fn is_immutable(&self, r: DescId) -> bool {
        matches!(self.p.arena.get(r), Desc::Con(n, a) if a.is_empty() && *n == self.immutable)
    }

    fn pure(&mut self) -> DescId {
        self.arena().desc(Desc::Pure)
    }

    fn con(&mut self, name: Sym) -> DescId {
        self.arena().con0(name)
    }

    // -------------------------------------------------------------- types
    /// The least upper bound of a set of types, as `max-of-types`: whichever is
    /// the supertype, or an error. FX-87 computes no joins — two types that are
    /// merely compatible are simply incomparable, which is why
    /// `(if #t 1 #\a)` does not check.
    fn max_of_types(&mut self, span: Span, types: &[DescId], what: &str) -> R<DescId> {
        let mut best = types[0];
        for t in &types[1..] {
            let (a, b) = (*t, best);
            best = {
                let rel = self.rel();
                if rel.type_less(a, b, &Default::default(), &Default::default()) {
                    b
                } else if rel.type_less(b, a, &Default::default(), &Default::default()) {
                    a
                } else {
                    return Err(FxError::cannot_type_check(span, what));
                }
            };
        }
        Ok(best)
    }

    /// Evaluate a written description into the description it denotes.
    fn eval(&mut self, d: DescId) -> DescId {
        let store = self.store.clone();
        eval::eval(&mut self.p.arena, &store, d)
    }

    // --------------------------------------------------------------- main
    pub fn desc_of_exp(&mut self, exp: ExpId, env: &TkEnv) -> R<Desc2> {
        let span = self.p.arena.span(exp);
        let what = || String::from("this expression");
        match self.p.arena.exp_at(exp).clone() {
            Exp::Int(_) => self.literal(self.p.syms.int),
            Exp::Float(_) => self.literal(self.p.syms.float),
            Exp::Char(_) => self.literal(self.p.syms.char),
            Exp::Bool(_) => self.literal(self.p.syms.bool),
            Exp::Unit => self.literal(self.p.syms.unit_type),
            // Quoted data and bare symbols are both `symbol`, which is what the
            // goldens record for `'()` too — see docs/divergences.md.
            Exp::Symbol(_) | Exp::Quote(_) => self.literal(self.p.syms.symbol),
            Exp::Str(_) => {
                let region = self.con(self.p.syms.region_eq);
                let string = self.p.syms.string;
                let ty = self.arena().desc(Desc::Con(string, vec![region]));
                let effect = self.pure();
                Ok(Desc2 { ty, effect })
            }

            Exp::Var(name) => {
                let Some(binding) = env.value(name).cloned() else {
                    return Err(FxError::syntax(
                        span,
                        format!("This variable has no type {}", self.p.interner.name(name)),
                    ));
                };
                let effect = self.effect_on(span, EffectKind::Read, binding.region)?;
                Ok(Desc2 { ty: binding.ty, effect })
            }

            Exp::The { effect, ty, body } => {
                let inner = self.desc_of_exp(body, env)?;
                let want_ty = self.eval(ty);
                let want_effect = match effect {
                    Some(e) => {
                        let e = self.eval(e);
                        self.purify_effect(e)?
                    }
                    // `(the type exp)` keeps whatever effect the body had.
                    None => inner.effect,
                };
                let ok = {
                    let rel = self.rel();
                    rel.type_less(inner.ty, want_ty, &Default::default(), &Default::default())
                        && rel.effect_less(
                            inner.effect,
                            want_effect,
                            &Default::default(),
                            &Default::default(),
                        )
                };
                if !ok {
                    return Err(FxError::cannot_type_check(span, &what()));
                }
                Ok(Desc2 { ty: want_ty, effect: want_effect })
            }

            Exp::If { test, then, els } => {
                let t = self.desc_of_exp(test, env)?;
                let is_bool = matches!(
                    self.p.arena.get(t.ty),
                    Desc::Con(n, a) if a.is_empty() && *n == self.p.syms.bool
                );
                if !is_bool {
                    return Err(FxError::cannot_type_check(span, &what()));
                }
                let a = self.desc_of_exp(then, env)?;
                let b = self.desc_of_exp(els, env)?;
                let ty = self.max_of_types(span, &[a.ty, b.ty], &what())?;
                let effect = self.arena().maxeff(vec![t.effect, a.effect, b.effect]);
                Ok(Desc2 { ty, effect })
            }

            Exp::Begin(items) => {
                if items.is_empty() {
                    let ty = self.con(self.p.syms.unit_type);
                    let effect = self.pure();
                    return Ok(Desc2 { ty, effect });
                }
                let mut effects = Vec::with_capacity(items.len());
                let mut last = None;
                for item in &items {
                    let d = self.desc_of_exp(*item, env)?;
                    effects.push(d.effect);
                    last = Some(d);
                }
                let last = last.expect("non-empty");
                let effect = self.arena().maxeff(effects);
                let masked = self.mask(exp, env, effect, last.ty);
                Ok(Desc2 { ty: last.ty, effect: masked })
            }

            Exp::Lambda { params, body } => self.lambda(span, &params, body, env),

            Exp::Let { bindings, body } => {
                // Initialisers are checked outside the scope.
                let mut inner = env.child();
                let mut effects = Vec::with_capacity(bindings.len() + 1);
                for b in &bindings {
                    let d = self.desc_of_exp(b.value, env)?;
                    effects.push(d.effect);
                    let region = self.binding_region(b.region);
                    if let Some(r) = b.region {
                        let alloc = self.effect_on(span, EffectKind::Alloc, r)?;
                        effects.push(alloc);
                    }
                    inner.bind_value(b.name, ValueBinding { ty: d.ty, region });
                }
                let d = self.desc_of_exp(body, &inner)?;
                effects.push(d.effect);
                let effect = self.arena().maxeff(effects);
                let masked = self.mask(exp, env, effect, d.ty);
                Ok(Desc2 { ty: d.ty, effect: masked })
            }

            Exp::Letrec { bindings, body } => self.letrec(exp, span, &bindings, body, env),

            Exp::App { fun, args } => self.app(exp, span, fun, &args, env),

            Exp::SetBang { name, value } => {
                let Some(binding) = env.value(name).cloned() else {
                    return Err(FxError::cannot_type_check(span, &what()));
                };
                let d = self.desc_of_exp(value, env)?;
                let ok = {
                    let rel = self.rel();
                    rel.type_less(d.ty, binding.ty, &Default::default(), &Default::default())
                };
                if !ok {
                    return Err(FxError::cannot_type_check(span, &what()));
                }
                let w = self.effect_on(span, EffectKind::Write, binding.region)?;
                let effect = self.arena().maxeff(vec![d.effect, w]);
                let ty = self.con(self.p.syms.unit_type);
                Ok(Desc2 { ty, effect })
            }

            Exp::PLambda { binders, body } => {
                let mut inner = env.child();
                for b in &binders {
                    inner.bind_desc(b.name, b.kind.clone());
                }
                let d = self.desc_of_exp(body, &inner)?;
                let ty = self.arena().desc(Desc::Poly { binders, body: d.ty });
                let effect = self.pure();
                Ok(Desc2 { ty, effect })
            }

            Exp::Proj { body, args } => {
                let d = self.desc_of_exp(body, env)?;
                let ty = self.project(span, d.ty, &args)?;
                Ok(Desc2 { ty, effect: d.effect })
            }
        }
    }

    fn literal(&mut self, name: Sym) -> R<Desc2> {
        let ty = self.con(name);
        let effect = self.pure();
        Ok(Desc2 { ty, effect })
    }

    /// An unannotated binding lives in the immutable region.
    fn binding_region(&mut self, given: Option<DescId>) -> DescId {
        match given {
            Some(r) => r,
            None => self.con(self.immutable),
        }
    }

    fn lambda(&mut self, span: Span, params: &[Param], body: ExpId, env: &TkEnv) -> R<Desc2> {
        let mut inner = env.child();
        let mut arg_types = Vec::with_capacity(params.len());
        let mut allocs = Vec::new();
        for p in params {
            let ty = self.eval(p.ty);
            arg_types.push(ty);
            let region = self.binding_region(p.region);
            if p.region.is_some() {
                allocs.push(self.effect_on(span, EffectKind::Alloc, region)?);
            }
            inner.bind_value(p.name, ValueBinding { ty, region });
        }
        let d = self.desc_of_exp(body, &inner)?;
        let mut effects = vec![d.effect];
        effects.extend(allocs);
        let raw = self.arena().maxeff(effects);
        // The parameters' regions are private to the body unless they escape,
        // so masking happens *inside* the arrow.
        let latent = self.mask_with(body, &inner, raw, d.ty, &params.iter().map(|p| p.name).collect::<Vec<_>>());
        let ty = self.arena().desc(Desc::Subr { effect: latent, args: arg_types, result: d.ty });
        // A lambda does nothing until it is applied.
        let effect = self.pure();
        Ok(Desc2 { ty, effect })
    }

    fn letrec(
        &mut self,
        exp: ExpId,
        span: Span,
        bindings: &[Binding],
        body: ExpId,
        env: &TkEnv,
    ) -> R<Desc2> {
        // A `letrec` binding must be typable without knowing its own type,
        // which in a checking system means the initialisers carry their types
        // themselves — a `lambda` with written parameters, or a `the`.
        let mut inner = env.child();
        for b in bindings {
            if let Some(ty) = self.written_type(b.value, env)? {
                let region = self.binding_region(b.region);
                inner.bind_value(b.name, ValueBinding { ty, region });
            }
        }
        let mut effects = Vec::new();
        for b in bindings {
            let d = self.desc_of_exp(b.value, &inner)?;
            effects.push(d.effect);
            let region = self.binding_region(b.region);
            inner.bind_value(b.name, ValueBinding { ty: d.ty, region });
        }
        let d = self.desc_of_exp(body, &inner)?;
        effects.push(d.effect);
        let effect = self.arena().maxeff(effects);
        let masked = self.mask(exp, env, effect, d.ty);
        let _ = span;
        Ok(Desc2 { ty: d.ty, effect: masked })
    }

    /// The type a `letrec` initialiser announces without being checked.
    ///
    /// A `lambda` states its argument types, and its result type is whatever
    /// its body turns out to be — which is not known yet. So only a `the`
    /// gives a complete answer here; a plain `lambda` is left to the second
    /// pass, which is enough for the self-recursive case the corpus uses,
    /// where the recursive call sits under a `the`.
    fn written_type(&mut self, exp: ExpId, _env: &TkEnv) -> R<Option<DescId>> {
        match self.p.arena.exp_at(exp).clone() {
            Exp::The { ty, .. } => Ok(Some(self.eval(ty))),
            _ => Ok(None),
        }
    }

    fn app(
        &mut self,
        exp: ExpId,
        span: Span,
        fun: ExpId,
        args: &[ExpId],
        env: &TkEnv,
    ) -> R<Desc2> {
        let f = self.desc_of_exp(fun, env)?;
        let mut arg_descs = Vec::with_capacity(args.len());
        for a in args {
            arg_descs.push(self.desc_of_exp(*a, env)?);
        }
        let what = unparse(&self.p.arena, &self.p.interner, f.ty);

        let mut fun_ty = self.eval(f.ty);
        // Implicit projection: a `poly` operator applied directly is
        // instantiated by matching its argument types against the actual ones,
        // so `(new 3)` need not be written `((proj (proj new @=) int) 3)`.
        if matches!(self.p.arena.get(fun_ty), Desc::Poly { .. }) {
            let actuals: Vec<DescId> = arg_descs.iter().map(|d| d.ty).collect();
            fun_ty = self.implicit_projection(span, fun_ty, &actuals, &what)?;
        }
        let Desc::Subr { effect: latent, args: formals, result } =
            self.p.arena.get(fun_ty).clone()
        else {
            return Err(FxError::cannot_type_check(span, &what));
        };
        if formals.len() != arg_descs.len() {
            return Err(FxError::cannot_type_check(span, &what));
        }
        for (actual, formal) in arg_descs.iter().zip(&formals) {
            let ok = {
                let rel = self.rel();
                rel.type_less(actual.ty, *formal, &Default::default(), &Default::default())
            };
            if !ok {
                return Err(FxError::cannot_type_check(span, &what));
            }
        }
        let latent = self.purify_effect(latent)?;
        let mut effects = vec![f.effect, latent];
        effects.extend(arg_descs.iter().map(|d| d.effect));
        let effect = self.arena().maxeff(effects);
        let masked = self.mask(exp, env, effect, result);
        Ok(Desc2 { ty: result, effect: masked })
    }

    /// Instantiate a `poly` operator from the types of its actual arguments.
    ///
    /// `extract-proj-info` peels every nested `poly` at once — `new` is a
    /// `poly` over a region wrapping a `poly` over a type — and the binders all
    /// become unknowns to be solved by matching the formal argument types
    /// against the actual ones. The match is one-way: only the formals contain
    /// unknowns, so this is matching rather than unification, and FX-87 needs
    /// nothing stronger because the actuals are always already known.
    ///
    /// A binder the arguments do not mention is left over. A **region** binder
    /// then takes the immutable region, which is what makes `(new 3)` come out
    /// `(ref int @=)` and therefore pure; anything else is genuinely ambiguous.
    fn implicit_projection(
        &mut self,
        span: Span,
        ty: DescId,
        actuals: &[DescId],
        what: &str,
    ) -> R<DescId> {
        let mut binders = Vec::new();
        let mut head = ty;
        while let Desc::Poly { binders: bs, body } = self.p.arena.get(head).clone() {
            binders.extend(bs);
            head = self.eval(body);
        }
        let formals = match self.p.arena.get(head).clone() {
            Desc::Subr { args, .. } => args,
            // A `vsubr` takes every argument at the same type.
            Desc::Vsubr { rest, .. } => vec![rest; actuals.len()],
            _ => return Err(FxError::cannot_type_check(span, what)),
        };
        if formals.len() != actuals.len() {
            return Err(FxError::cannot_type_check(span, what));
        }
        let names: HashSet<Sym> = binders.iter().map(|b| b.name).collect();
        let mut solution = std::collections::HashMap::new();
        for (formal, actual) in formals.iter().zip(actuals) {
            if !self.match_desc(*formal, *actual, &names, &mut solution, &mut Vec::new()) {
                return Err(FxError::cannot_type_check(span, what));
            }
        }
        for b in &binders {
            if solution.contains_key(&b.name) {
                continue;
            }
            if b.kind == Kind::Region {
                let r = self.con(self.immutable);
                solution.insert(b.name, r);
            } else {
                return Err(FxError::cannot_type_check(span, what));
            }
        }
        let instantiated = eval::substitute(&mut self.p.arena, head, &solution);
        Ok(self.eval(instantiated))
    }

    /// One-way structural match of a formal against an actual.
    fn match_desc(
        &mut self,
        formal: DescId,
        actual: DescId,
        vars: &HashSet<Sym>,
        out: &mut std::collections::HashMap<Sym, DescId>,
        trail: &mut Vec<(DescId, DescId)>,
    ) -> bool {
        if trail.contains(&(formal, actual)) {
            return true;
        }
        if let Desc::Var(v) = self.p.arena.get(formal).clone()
            && vars.contains(&v)
        {
            return match out.get(&v) {
                Some(bound) => {
                    let rel = self.rel();
                    rel.desc_equal(*bound, actual, &Default::default(), &Default::default())
                }
                None => {
                    out.insert(v, actual);
                    true
                }
            };
        }
        trail.push((formal, actual));
        let result = match (self.p.arena.get(formal).clone(), self.p.arena.get(actual).clone()) {
            (Desc::Con(n1, a1), Desc::Con(n2, a2)) => {
                n1 == n2
                    && a1.len() == a2.len()
                    && a1
                        .iter()
                        .zip(&a2)
                        .all(|(x, y)| self.match_desc(*x, *y, vars, out, trail))
            }
            (
                Desc::Subr { effect: e1, args: s1, result: r1 },
                Desc::Subr { effect: e2, args: s2, result: r2 },
            ) => {
                s1.len() == s2.len()
                    && self.match_desc(e1, e2, vars, out, trail)
                    && s1
                        .iter()
                        .zip(&s2)
                        .all(|(x, y)| self.match_desc(*x, *y, vars, out, trail))
                    && self.match_desc(r1, r2, vars, out, trail)
            }
            (Desc::Read(a), Desc::Read(b))
            | (Desc::Write(a), Desc::Write(b))
            | (Desc::Alloc(a), Desc::Alloc(b)) => self.match_desc(a, b, vars, out, trail),
            (Desc::Pure, Desc::Pure) => true,
            (
                Desc::RecordOf { fields: f1, region: g1 },
                Desc::RecordOf { fields: f2, region: g2 },
            )
            | (
                Desc::OneOf { variants: f1, region: g1 },
                Desc::OneOf { variants: f2, region: g2 },
            ) => {
                f1.len() == f2.len()
                    && f1.iter().zip(&f2).all(|((n1, x), (n2, y))| {
                        n1 == n2 && self.match_desc(*x, *y, vars, out, trail)
                    })
                    && self.match_desc(g1, g2, vars, out, trail)
            }
            _ => {
                let rel = self.rel();
                rel.desc_equal(formal, actual, &Default::default(), &Default::default())
            }
        };
        trail.pop();
        result
    }

    /// `(proj e d…)` — instantiate a `poly`, one binder group at a time.
    fn project(&mut self, span: Span, ty: DescId, args: &[DescId]) -> R<DescId> {
        let mut current = self.eval(ty);
        for arg in args {
            let Desc::Poly { binders, body } = self.p.arena.get(current).clone() else {
                return Err(FxError::cannot_type_check(span, "projection of a non-poly"));
            };
            if binders.len() != 1 {
                // Several binders at once are supplied by several `proj`
                // arguments in order, which is how the corpus writes them.
                return Err(FxError::cannot_type_check(span, "arity in projection"));
            }
            let evaluated = self.eval(*arg);
            let map = std::iter::once((binders[0].name, evaluated)).collect();
            current = eval::substitute(&mut self.p.arena, body, &map);
            current = self.eval(current);
        }
        Ok(current)
    }

    // ------------------------------------------------------------ masking
    fn mask(&mut self, exp: ExpId, env: &TkEnv, effect: DescId, result: DescId) -> DescId {
        self.mask_with(exp, env, effect, result, &[])
    }

    /// Mask `effect`, treating the regions of everything free in `exp` — apart
    /// from `bound` — as escaping.
    fn mask_with(
        &mut self,
        exp: ExpId,
        env: &TkEnv,
        effect: DescId,
        result: DescId,
        bound: &[Sym],
    ) -> DescId {
        let mut free = HashSet::new();
        self.free_vars(exp, &mut free);
        let mut visible = Vec::new();
        for name in free {
            if bound.contains(&name) {
                continue;
            }
            if let Some(b) = env.value(name) {
                visible.push(b.region);
                visible.push(b.ty);
            }
        }
        let (imm, rf) = (self.immutable, self.ref_name);
        erase_effect(&mut self.p.arena, imm, rf, effect, result, &visible)
    }

    fn free_vars(&self, exp: ExpId, out: &mut HashSet<Sym>) {
        match self.p.arena.exp_at(exp) {
            Exp::Var(v) => {
                out.insert(*v);
            }
            Exp::SetBang { name, value } => {
                out.insert(*name);
                self.free_vars(*value, out);
            }
            Exp::The { body, .. } | Exp::PLambda { body, .. } | Exp::Proj { body, .. } => {
                self.free_vars(*body, out)
            }
            Exp::If { test, then, els } => {
                self.free_vars(*test, out);
                self.free_vars(*then, out);
                self.free_vars(*els, out);
            }
            Exp::Begin(items) => {
                for i in items {
                    self.free_vars(*i, out);
                }
            }
            Exp::Lambda { params, body } => {
                let mut inner = HashSet::new();
                self.free_vars(*body, &mut inner);
                for p in params {
                    inner.remove(&p.name);
                }
                out.extend(inner);
            }
            Exp::Let { bindings, body } | Exp::Letrec { bindings, body } => {
                let mut inner = HashSet::new();
                self.free_vars(*body, &mut inner);
                for b in bindings {
                    self.free_vars(b.value, out);
                    inner.remove(&b.name);
                }
                out.extend(inner);
            }
            Exp::App { fun, args } => {
                self.free_vars(*fun, out);
                for a in args {
                    self.free_vars(*a, out);
                }
            }
            _ => {}
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq)]
enum EffectKind {
    Read,
    Write,
    Alloc,
}

/// Keeps the kind and binder types referenced while the checker grows.
#[allow(dead_code)]
fn _unused(_: Kind, _: Binder) {}
