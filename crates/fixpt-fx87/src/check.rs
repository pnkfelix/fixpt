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

use crate::ast::{
    Arena, Binder, Binding, Desc, DescId, DoBinding, Exp, ExpId, Kind, Param, TagClause,
};
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
    fn max_of_types(&mut self, exp: ExpId, types: &[DescId]) -> R<DescId> {
        let mut best = types[0];
        for t in &types[1..] {
            let (a, b) = (*t, best);
            let ordered = {
                let rel = self.rel();
                if rel.type_less(a, b, &Default::default(), &Default::default()) {
                    Some(b)
                } else if rel.type_less(b, a, &Default::default(), &Default::default()) {
                    Some(a)
                } else {
                    None
                }
            };
            best = match ordered {
                Some(x) => x,
                None => {
                    // Raised, not declined — and note the argument order the
                    // reference prints: the incoming type first.
                    let msg = format!(
                        "Uncomparable types {} {}",
                        self.show_desc(a),
                        self.show_desc(b)
                    );
                    return Err(self.raised(exp, msg));
                }
            };
        }
        Ok(best)
    }

    /// Evaluate a written description into the description it denotes.
    ///
    /// Head expansion only: the arguments are expanded as they are reached, and
    /// forcing a whole recursive type eagerly would not terminate.
    fn eval(&mut self, d: DescId) -> DescId {
        let store = self.store.clone();
        eval::eval(&mut self.p.arena, &store, d)
    }

    /// Evaluate a description *throughout*, so that what is printed is what it
    /// means at every level.
    ///
    /// Head expansion is enough to compare two descriptions, because comparison
    /// expands as it descends. It is not enough to *print* one: `reverse`
    /// returns `(listof int r2)` nested inside a `poly`, and the goldens record
    /// the recursive pair type that denotes. The same walk purifies effects
    /// buried in a type, which is why `(subr (read @=) (int) int)` prints as
    /// `(subr pure (int) int)`.
    ///
    /// Cycle-safe by the same means as substitution: a hole is allocated before
    /// the children are walked, so a recursive occurrence finds it.
    fn eval_deep(&mut self, d: DescId) -> DescId {
        let mut memo = std::collections::HashMap::new();
        self.eval_deep_memo(d, &mut memo)
    }

    fn eval_deep_memo(
        &mut self,
        d: DescId,
        memo: &mut std::collections::HashMap<DescId, DescId>,
    ) -> DescId {
        if let Some(done) = memo.get(&d) {
            return *done;
        }
        let expanded = self.eval(d);
        if let Some(done) = memo.get(&expanded) {
            return *done;
        }
        let hole = self.arena().hole();
        memo.insert(d, hole);
        memo.insert(expanded, hole);
        let rebuilt = match self.p.arena.get(expanded).clone() {
            Desc::Var(v) => Desc::Var(v),
            Desc::Pure => Desc::Pure,
            Desc::Hole => Desc::Hole,
            Desc::Con(n, args) => {
                Desc::Con(n, args.iter().map(|a| self.eval_deep_memo(*a, memo)).collect())
            }
            Desc::Subr { effect, args, result } => Desc::Subr {
                effect: self.eval_deep_memo(effect, memo),
                args: args.iter().map(|a| self.eval_deep_memo(*a, memo)).collect(),
                result: self.eval_deep_memo(result, memo),
            },
            Desc::Vsubr { effect, args, rest, result } => Desc::Vsubr {
                effect: self.eval_deep_memo(effect, memo),
                args: args.iter().map(|a| self.eval_deep_memo(*a, memo)).collect(),
                rest: self.eval_deep_memo(rest, memo),
                result: self.eval_deep_memo(result, memo),
            },
            Desc::Poly { binders, body } => {
                Desc::Poly { binders, body: self.eval_deep_memo(body, memo) }
            }
            Desc::DAbs { binders, body } => {
                Desc::DAbs { binders, body: self.eval_deep_memo(body, memo) }
            }
            Desc::RecordOf { fields, region } => Desc::RecordOf {
                fields: fields.iter().map(|(n, t)| (*n, self.eval_deep_memo(*t, memo))).collect(),
                region: self.eval_deep_memo(region, memo),
            },
            Desc::OneOf { variants, region } => Desc::OneOf {
                variants: variants
                    .iter()
                    .map(|(n, t)| (*n, self.eval_deep_memo(*t, memo)))
                    .collect(),
                region: self.eval_deep_memo(region, memo),
            },
            // An effect on the immutable region is `pure` wherever it appears,
            // not only at the top of a description.
            Desc::Read(r) | Desc::Write(r) | Desc::Alloc(r) if self.is_immutable(r) => Desc::Pure,
            Desc::Read(r) => Desc::Read(self.eval_deep_memo(r, memo)),
            Desc::Write(r) => Desc::Write(self.eval_deep_memo(r, memo)),
            Desc::Alloc(r) => Desc::Alloc(self.eval_deep_memo(r, memo)),
            Desc::MaxEff(parts) => {
                let walked: Vec<DescId> =
                    parts.iter().map(|p| self.eval_deep_memo(*p, memo)).collect();
                let merged = self.arena().maxeff(walked);
                self.p.arena.get(merged).clone()
            }
            Desc::RUnion(parts) => {
                let walked: Vec<DescId> =
                    parts.iter().map(|p| self.eval_deep_memo(*p, memo)).collect();
                let merged = self.arena().runion(walked);
                self.p.arena.get(merged).clone()
            }
            Desc::DApp { fun, args } => Desc::DApp {
                fun: self.eval_deep_memo(fun, memo),
                args: args.iter().map(|a| self.eval_deep_memo(*a, memo)).collect(),
            },
        };
        self.arena().fill(hole, rebuilt);
        hole
    }

    /// Check a top-level expression and report its description.
    ///
    /// The difference from [`desc_of_exp`](Checker::desc_of_exp) is the deep
    /// evaluation: internally a description need only be expanded far enough to
    /// compare, but what is *reported* has to be what it means throughout.
    pub fn check(&mut self, exp: ExpId, env: &TkEnv) -> R<Desc2> {
        let d = self.desc_of_exp(exp, env)?;
        let ty = self.eval_deep(d.ty);
        let effect = self.eval_deep(d.effect);
        Ok(Desc2 { ty, effect })
    }

    // --------------------------------------------------------------- main
    pub fn desc_of_exp(&mut self, exp: ExpId, env: &TkEnv) -> R<Desc2> {
        let span = self.p.arena.span(exp);
        match self.p.arena.exp_at(exp).clone() {
            Exp::Int(_) => self.literal(self.p.syms.int),
            // `literal-int?` tests Scheme's `integer?`, which is true of
            // `1.0`, and it is checked *before* `literal-float?`. So `1.0` is
            // an `int` and `(fl+ 1.0 2.5)` is a type error — a property of
            // Scheme's `integer?` rather than of the port, and therefore
            // faithful to 1987. See docs/divergences.md.
            Exp::Float(bits) => {
                let f = f64::from_bits(bits);
                let name =
                    if f.is_finite() && f.fract() == 0.0 { self.p.syms.int } else { self.p.syms.float };
                self.literal(name)
            }
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
                    return Err(self.raised(
                        exp,
                        format!(
                            "This variable has no type {}",
                            self.p.interner.name(name)
                        ),
                    ));
                };
                let effect = self.effect_on(span, EffectKind::Read, binding.region)?;
                Ok(Desc2 { ty: binding.ty, effect })
            }

            Exp::The { effect, ty, body } => {
                let inner = self.desc_of_exp(body, env)?;
                // Fully, not just at the head: the ascription may bury an
                // effect on the immutable region, and `(subr (read @=) …)` has
                // to compare equal to `(subr pure …)`.
                let want_ty = self.eval_deep(ty);
                let want_effect = match effect {
                    Some(e) => {
                        let e = self.eval(e);
                        self.purify_effect(e)?
                    }
                    // `(the type exp)` keeps whatever effect the body had.
                    None => inner.effect,
                };
                let type_ok = {
                    let rel = self.rel();
                    rel.type_less(inner.ty, want_ty, &Default::default(), &Default::default())
                };
                if !type_ok {
                    let msg = format!(
                        "Subtyping rule violation {} {}",
                        self.show_desc(inner.ty),
                        self.show_desc(want_ty)
                    );
                    return Err(self.raised(exp, msg));
                }
                let effect_ok = {
                    let rel = self.rel();
                    rel.effect_less(
                        inner.effect,
                        want_effect,
                        &Default::default(),
                        &Default::default(),
                    )
                };
                if !effect_ok {
                    let msg = format!(
                        "Subeffecting rule violation {} {}",
                        self.show_desc(inner.effect),
                        self.show_desc(want_effect)
                    );
                    return Err(self.raised(exp, msg));
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
                    // `desc-of-if` returns falsy here rather than raising, so
                    // this is the generic message with the form quoted.
                    return Err(self.declined(exp));
                }
                let a = self.desc_of_exp(then, env)?;
                let b = self.desc_of_exp(els, env)?;
                let ty = self.max_of_types(exp, &[a.ty, b.ty])?;
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

            Exp::Letrec { bindings, body } => self.letrec(exp, &bindings, body, env),

            Exp::App { fun, args } => self.app(exp, fun, &args, env),

            Exp::SetBang { name, value } => {
                let Some(binding) = env.value(name).cloned() else {
                    return Err(self.raised(
                        exp,
                        format!(
                            "This variable has no type {}",
                            self.p.interner.name(name)
                        ),
                    ));
                };
                let d = self.desc_of_exp(value, env)?;
                let ok = {
                    let rel = self.rel();
                    rel.type_less(d.ty, binding.ty, &Default::default(), &Default::default())
                };
                if !ok {
                    let msg = format!(
                        "Subtyping rule violation {} {}",
                        self.show_desc(d.ty),
                        self.show_desc(binding.ty)
                    );
                    return Err(self.raised(exp, msg));
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

            // ------------------------------------------- standard forms
            Exp::Record { fields, region } => {
                let region = self.binding_region(region);
                let mut effects = Vec::with_capacity(fields.len() + 1);
                let mut types = Vec::with_capacity(fields.len());
                for (name, value) in &fields {
                    let d = self.desc_of_exp(*value, env)?;
                    effects.push(d.effect);
                    types.push((*name, d.ty));
                }
                // A record is allocated, so building one costs `(alloc r)` —
                // purified away when it lives in the immutable region.
                let alloc = self.effect_on(span, EffectKind::Alloc, region)?;
                effects.push(alloc);
                let ty = self.arena().desc(Desc::RecordOf { fields: types, region });
                let effect = self.arena().maxeff(effects);
                Ok(Desc2 { ty, effect })
            }

            Exp::Select { rec, field } => {
                let d = self.desc_of_exp(rec, env)?;
                let rec_ty = self.eval(d.ty);
                let Desc::RecordOf { fields, region } = self.p.arena.get(rec_ty).clone() else {
                    return Err(self.declined(exp));
                };
                let Some((_, ty)) = fields.iter().find(|(n, _)| *n == field).copied() else {
                    // No such field: the rule declines, so this is the generic
                    // message — which is what the corpus records.
                    return Err(self.declined(exp));
                };
                let read = self.effect_on(span, EffectKind::Read, region)?;
                let effect = self.arena().maxeff(vec![read, d.effect]);
                Ok(Desc2 { ty, effect })
            }

            Exp::RecordSet { rec, field, value } => {
                let d = self.desc_of_exp(rec, env)?;
                let v = self.desc_of_exp(value, env)?;
                let rec_ty = self.eval(d.ty);
                let Desc::RecordOf { fields, region } = self.p.arena.get(rec_ty).clone() else {
                    return Err(self.declined(exp));
                };
                if self.is_immutable(region) {
                    return Err(self.raised(exp, "Use RECORD-SET! on mutable region only"));
                }
                let Some((_, want)) = fields.iter().find(|(n, _)| *n == field).copied() else {
                    return Err(self.declined(exp));
                };
                let ok = {
                    let rel = self.rel();
                    rel.type_less(v.ty, want, &Default::default(), &Default::default())
                };
                if !ok {
                    return Err(self.declined(exp));
                }
                let write = self.effect_on(span, EffectKind::Write, region)?;
                let effect = self.arena().maxeff(vec![write, d.effect, v.effect]);
                let ty = self.con(self.p.syms.unit_type);
                Ok(Desc2 { ty, effect })
            }

            Exp::One { ty, tag, value } => {
                let d = self.desc_of_exp(value, env)?;
                let one_ty = self.eval(ty);
                let Desc::OneOf { variants, region } = self.p.arena.get(one_ty).clone() else {
                    return Err(self.raised(exp, "Not a ONEOF type:"));
                };
                let Some((_, want)) = variants.iter().find(|(n, _)| *n == tag).copied() else {
                    return Err(self.raised(
                        exp,
                        format!("Incompatible tag {}", self.p.interner.name(tag)),
                    ));
                };
                let ok = {
                    let rel = self.rel();
                    rel.type_less(d.ty, want, &Default::default(), &Default::default())
                };
                if !ok {
                    return Err(self.declined(exp));
                }
                let alloc = self.effect_on(span, EffectKind::Alloc, region)?;
                let effect = self.arena().maxeff(vec![alloc, d.effect]);
                Ok(Desc2 { ty: one_ty, effect })
            }

            Exp::OneSet { target, tag, value } => {
                let d = self.desc_of_exp(target, env)?;
                let v = self.desc_of_exp(value, env)?;
                let one_ty = self.eval(d.ty);
                let Desc::OneOf { variants, region } = self.p.arena.get(one_ty).clone() else {
                    return Err(self.declined(exp));
                };
                if self.is_immutable(region) {
                    return Err(self.raised(exp, "Use ONE-SET! on mutable region only"));
                }
                let Some((_, want)) = variants.iter().find(|(n, _)| *n == tag).copied() else {
                    return Err(self.declined(exp));
                };
                let ok = {
                    let rel = self.rel();
                    rel.type_less(v.ty, want, &Default::default(), &Default::default())
                };
                if !ok {
                    return Err(self.declined(exp));
                }
                let write = self.effect_on(span, EffectKind::Write, region)?;
                let effect = self.arena().maxeff(vec![write, d.effect, v.effect]);
                let ty = self.con(self.p.syms.unit_type);
                Ok(Desc2 { ty, effect })
            }

            Exp::TagCase { var, scrutinee, region, clauses } => {
                self.tagcase(exp, span, var, scrutinee, region, &clauses, env)
            }

            Exp::Delay(body) => {
                let d = self.desc_of_exp(body, env)?;
                // The body's effect becomes latent in the promise; forcing it
                // is what pays. Building the promise costs an allocation only
                // when there is something to defer.
                let promise = self.p.syms.promise;
                let ty = self.arena().desc(Desc::Con(promise, vec![d.effect, d.ty]));
                let effect = if matches!(self.p.arena.get(d.effect), Desc::Pure) {
                    self.pure()
                } else {
                    let r = self.con(self.immutable);
                    self.effect_on(span, EffectKind::Alloc, r)?
                };
                Ok(Desc2 { ty, effect })
            }

            Exp::VLambda { name, ty, region, body } => {
                // A `vlambda` is a `lambda` whose one parameter is a *list* of
                // the declared type, and whose type is a `vsubr`.
                let element = self.eval(ty);
                let listof = self.p.interner.intern("listof");
                let imm = self.con(self.immutable);
                let list_ty = self.arena().desc(Desc::Con(listof, vec![element, imm]));
                let list_ty = self.eval(list_ty);
                let mut inner = env.child();
                let binding_region = self.binding_region(region);
                inner.bind_value(name, ValueBinding { ty: list_ty, region: binding_region });
                let d = self.desc_of_exp(body, &inner)?;
                let mut effects = vec![d.effect];
                if region.is_some() {
                    effects.push(self.effect_on(span, EffectKind::Alloc, binding_region)?);
                }
                let raw = self.arena().maxeff(effects);
                let latent = self.mask_with(body, &inner, raw, d.ty, &[name]);
                let ty = self.arena().desc(Desc::Vsubr {
                    effect: latent,
                    args: Vec::new(),
                    rest: element,
                    result: d.ty,
                });
                let effect = self.pure();
                Ok(Desc2 { ty, effect })
            }

            Exp::Do { bindings, test, result, body } => {
                self.check_do(exp, span, &bindings, test, result, body, env)
            }

            Exp::Proj { body, args } => {
                let d = self.desc_of_exp(body, env)?;
                let ty = self.project(span, d.ty, &args)?;
                Ok(Desc2 { ty, effect: d.effect })
            }
        }
    }

    /// The offending form, rendered the way the reference's messages render it.
    ///
    /// `display` rather than `write`, so a symbol appears bare: the goldens say
    /// `Cannot type-check (select (record ((a 1) (b #t))) c)`, not `|#t|`.
    fn show(&self, exp: ExpId) -> String {
        match self.p.arena.source(exp) {
            Some(syntax) => fixpt_read::display_syntax(syntax, &self.p.interner),
            None => "this expression".to_string(),
        }
    }

    fn show_desc(&self, d: DescId) -> String {
        unparse(&self.p.arena, &self.p.interner, d)
    }

    /// A rule *declined*: `desc-of-exp-1` returned falsy, and `desc-of-exp`
    /// reports it generically with the form quoted. Distinct from a rule that
    /// raises its own message — the difference tells you which happened.
    fn declined(&self, exp: ExpId) -> FxError {
        let span = self.p.arena.span(exp);
        FxError::cannot_type_check(span, &self.show(exp))
    }

    /// A rule *raised*, with its own wording.
    fn raised(&self, exp: ExpId, message: impl Into<String>) -> FxError {
        let span = self.p.arena.span(exp);
        FxError { span, message: message.into(), user: true }
    }

    /// `(tagcase (v e) (tag body)… )` — each arm sees `v` at that tag's type.
    ///
    /// The `else` arm sees the *remaining* variants, but only when the value is
    /// immutable: if it can be written through, another tag could be stored
    /// behind the binding's back, so the arm has to assume the whole type.
    #[allow(clippy::too_many_arguments)]
    fn tagcase(
        &mut self,
        exp: ExpId,
        span: Span,
        var: Sym,
        scrutinee: ExpId,
        region: Option<DescId>,
        clauses: &[TagClause],
        env: &TkEnv,
    ) -> R<Desc2> {
        let d = self.desc_of_exp(scrutinee, env)?;
        let one_ty = self.eval(d.ty);
        let Desc::OneOf { variants, region: one_region } = self.p.arena.get(one_ty).clone() else {
            return Err(self.declined(exp));
        };
        let binding_region = match region {
            Some(r) => r,
            None => one_region,
        };
        let named: Vec<Sym> = clauses.iter().filter_map(|c| c.tag).collect();
        let mut effects = vec![d.effect];
        let mut types = Vec::with_capacity(clauses.len());
        for clause in clauses {
            let arm_ty = match clause.tag {
                Some(tag) => match variants.iter().find(|(n, _)| *n == tag).copied() {
                    Some((_, t)) => t,
                    None => return Err(self.declined(exp)),
                },
                None => {
                    let rest: Vec<(Sym, DescId)> = variants
                        .iter()
                        .filter(|(n, _)| !named.contains(n))
                        .copied()
                        .collect();
                    if self.is_immutable(one_region) {
                        self.arena().desc(Desc::OneOf { variants: rest, region: one_region })
                    } else {
                        one_ty
                    }
                }
            };
            let mut inner = env.child();
            inner.bind_value(var, ValueBinding { ty: arm_ty, region: binding_region });
            let arm = self.desc_of_exp(clause.body, &inner)?;
            effects.push(arm.effect);
            types.push(arm.ty);
        }
        if types.is_empty() {
            return Err(self.declined(exp));
        }
        let read = self.effect_on(span, EffectKind::Read, one_region)?;
        effects.push(read);
        let ty = self.max_of_types(exp, &types)?;
        let effect = self.arena().maxeff(effects);
        Ok(Desc2 { ty, effect })
    }

    /// `do`, whose loop variables take their types from their initialisers.
    #[allow(clippy::too_many_arguments)]
    fn check_do(
        &mut self,
        exp: ExpId,
        span: Span,
        bindings: &[DoBinding],
        test: ExpId,
        result: ExpId,
        body: Option<ExpId>,
        env: &TkEnv,
    ) -> R<Desc2> {
        let mut effects = Vec::new();
        let mut inner = env.child();
        for b in bindings {
            // The initialiser is checked *outside* the loop's scope.
            let d = self.desc_of_exp(b.init, env)?;
            effects.push(d.effect);
            let region = self.binding_region(b.region);
            if b.region.is_some() {
                effects.push(self.effect_on(span, EffectKind::Alloc, region)?);
            }
            inner.bind_value(b.name, ValueBinding { ty: d.ty, region });
        }
        let t = self.desc_of_exp(test, &inner)?;
        let is_bool = matches!(
            self.p.arena.get(t.ty),
            Desc::Con(n, a) if a.is_empty() && *n == self.p.syms.bool
        );
        if !is_bool {
            return Err(self.declined(exp));
        }
        effects.push(t.effect);
        // Each step has to stay within its variable's type, since it becomes
        // that variable's value next time round.
        for b in bindings {
            let Some(step) = b.step else { continue };
            let d = self.desc_of_exp(step, &inner)?;
            effects.push(d.effect);
            let want = inner.value(b.name).expect("just bound").ty;
            let ok = {
                let rel = self.rel();
                rel.type_less(d.ty, want, &Default::default(), &Default::default())
            };
            if !ok {
                return Err(self.declined(exp));
            }
        }
        if let Some(body) = body {
            let d = self.desc_of_exp(body, &inner)?;
            effects.push(d.effect);
        }
        let r = self.desc_of_exp(result, &inner)?;
        effects.push(r.effect);
        let effect = self.arena().maxeff(effects);
        let names: Vec<Sym> = bindings.iter().map(|b| b.name).collect();
        let masked = self.mask_with(exp, &inner, effect, r.ty, &names);
        Ok(Desc2 { ty: r.ty, effect: masked })
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
            let ty = self.eval_deep(p.ty);
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
        Ok(Desc2 { ty: d.ty, effect: masked })
    }

    /// The type a `letrec` initialiser announces without needing to be checked.
    ///
    /// Checking is what makes recursion tractable here: a recursive binding has
    /// to state its own type, and in FX-87 it does. A `lambda` writes its
    /// argument types, and when its body is a `the` it writes its result and
    /// effect too — which between them give the whole `subr`, so the recursive
    /// call inside can be checked against it.
    fn written_type(&mut self, exp: ExpId, _env: &TkEnv) -> R<Option<DescId>> {
        match self.p.arena.exp_at(exp).clone() {
            Exp::The { ty, .. } => Ok(Some(self.eval_deep(ty))),
            Exp::Lambda { params, body } => {
                let Exp::The { ty, effect, .. } = self.p.arena.exp_at(body).clone() else {
                    return Ok(None);
                };
                let Some(effect) = effect else { return Ok(None) };
                let effect = self.eval_deep(effect);
                let result = self.eval_deep(ty);
                let mut args = Vec::with_capacity(params.len());
                for p in &params {
                    args.push(self.eval_deep(p.ty));
                }
                Ok(Some(self.arena().desc(Desc::Subr { effect, args, result })))
            }
            _ => Ok(None),
        }
    }

    fn app(&mut self, exp: ExpId, fun: ExpId, args: &[ExpId], env: &TkEnv) -> R<Desc2> {
        let f = self.desc_of_exp(fun, env)?;
        let mut arg_descs = Vec::with_capacity(args.len());
        for a in args {
            arg_descs.push(self.desc_of_exp(*a, env)?);
        }
        let mut fun_ty = self.eval(f.ty);
        // Implicit projection: a `poly` operator applied directly is
        // instantiated by matching its argument types against the actual ones,
        // so `(new 3)` need not be written `((proj (proj new @=) int) 3)`.
        if matches!(self.p.arena.get(fun_ty), Desc::Poly { .. }) {
            let actuals: Vec<DescId> = arg_descs.iter().map(|d| d.ty).collect();
            fun_ty = self.implicit_projection(exp, fun_ty, &actuals)?;
        }
        // `(vsubr effect t result)` takes any number of arguments, all of type
        // `t` — which is how `list` is declared. Expanding it to a `subr` of
        // the right arity here means the checks below need no second form.
        if let Desc::Vsubr { effect, args, rest, result } = self.p.arena.get(fun_ty).clone() {
            let mut formals = args;
            while formals.len() < arg_descs.len() {
                formals.push(rest);
            }
            fun_ty = self.arena().desc(Desc::Subr { effect, args: formals, result });
        }
        let Desc::Subr { effect: latent, args: formals, result } =
            self.p.arena.get(fun_ty).clone()
        else {
            return Err(self.declined(exp));
        };
        if formals.len() != arg_descs.len() {
            return Err(self.raised(
                exp,
                format!("Incorrect number of args in {}", self.show(exp)),
            ));
        }
        let formals: Vec<DescId> = formals.iter().map(|f| self.eval(*f)).collect();
        let mismatched = arg_descs.iter().zip(&formals).any(|(actual, formal)| {
            let rel = self.rel();
            !rel.type_less(actual.ty, *formal, &Default::default(), &Default::default())
        });
        if mismatched {
            let actuals: Vec<String> = arg_descs.iter().map(|d| self.show_desc(d.ty)).collect();
            let wanted: Vec<String> = formals.iter().map(|f| self.show_desc(*f)).collect();
            let msg = format!(
                "Wrong arguments types (actuals formals): ({}) ({}) in {}",
                actuals.join(" "),
                wanted.join(" "),
                self.show(exp)
            );
            return Err(self.raised(exp, msg));
        }
        let latent = self.purify_effect(latent)?;
        let mut effects = vec![f.effect, latent];
        effects.extend(arg_descs.iter().map(|d| d.effect));
        let effect = self.arena().maxeff(effects);
        // The result as written may still be a constructor that denotes
        // something else — `string->list` returns `(listof char @=)`, which
        // *is* a recursive pair type.
        let result = self.eval(result);
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
        exp: ExpId,
        ty: DescId,
        actuals: &[DescId],
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
            _ => return Err(self.declined(exp)),
        };
        if formals.len() != actuals.len() {
            return Err(self.declined(exp));
        }
        let names: HashSet<Sym> = binders.iter().map(|b| b.name).collect();
        let mut solution = std::collections::HashMap::new();
        // The formals have to be evaluated before they can be matched: `length`
        // expects `(listof t r)`, while the actual from `(list 1 2 3)` is
        // already the recursive pair type that denotes. Matching one against
        // the other without expanding first compares a constructor with its own
        // meaning and fails.
        let formals: Vec<DescId> = formals.iter().map(|f| self.eval(*f)).collect();
        for (formal, actual) in formals.iter().zip(actuals) {
            if !self.match_desc(*formal, *actual, &names, &mut solution, &mut Vec::new()) {
                // The reference reports this as an ordinary argument-type
                // failure once the projection has been chosen, so the message
                // is built by the caller rather than here.
                return Err(self.declined(exp));
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
                return Err(self.raised(
                    exp,
                    format!("ambiguous implicit projection {}", self.show(exp)),
                ));
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
            let _ = &span;
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
        let immutable = self.con(self.immutable);
        for name in free {
            let Some(b) = env.value(name) else { continue };
            // A free variable's *type* always contributes its regions, even
            // when the variable is one this scope binds: a parameter of type
            // `(ref int @!)` was handed in by the caller, who can therefore
            // observe what is done to `@!`. Note *regions within* the type —
            // the type itself is not a region and would never compare equal to
            // one.
            let (ty, region) = (b.ty, b.region);
            visible.extend(crate::mask::regions_in(&self.p.arena, ty));
            // `dont-count` in the reference does not drop the variable — it
            // substitutes the immutable region for its *binding* region, so
            // merely being bound here does not make the binding observable.
            let effective = if bound.contains(&name) { immutable } else { region };
            visible.extend(crate::mask::regions_in(&self.p.arena, effective));
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
            Exp::Record { fields, .. } => {
                for (_, e) in fields {
                    self.free_vars(*e, out);
                }
            }
            Exp::Select { rec, .. } => self.free_vars(*rec, out),
            Exp::RecordSet { rec, value, .. } | Exp::OneSet { target: rec, value, .. } => {
                self.free_vars(*rec, out);
                self.free_vars(*value, out);
            }
            Exp::One { value, .. } => self.free_vars(*value, out),
            Exp::Delay(e) => self.free_vars(*e, out),
            Exp::TagCase { var, scrutinee, clauses, .. } => {
                self.free_vars(*scrutinee, out);
                let mut inner = HashSet::new();
                for c in clauses {
                    self.free_vars(c.body, &mut inner);
                }
                inner.remove(var);
                out.extend(inner);
            }
            Exp::VLambda { name, body, .. } => {
                let mut inner = HashSet::new();
                self.free_vars(*body, &mut inner);
                inner.remove(name);
                out.extend(inner);
            }
            Exp::Do { bindings, test, result, body } => {
                let mut inner = HashSet::new();
                self.free_vars(*test, &mut inner);
                self.free_vars(*result, &mut inner);
                if let Some(b) = body {
                    self.free_vars(*b, &mut inner);
                }
                for b in bindings {
                    self.free_vars(b.init, out);
                    if let Some(step) = b.step {
                        self.free_vars(step, &mut inner);
                    }
                    inner.remove(&b.name);
                }
                out.extend(inner);
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
