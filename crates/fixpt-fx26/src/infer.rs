//! Bidirectional checking: what an expression is *expected* to be, used.
//!
//! [`synth`](Checker::synth) says what an expression is; [`check`](Checker::check)
//! is told what it should be, and uses that to fill in what the program left
//! out. Two things can be left out:
//!
//! * **A `lambda`'s parameter types**, when the `lambda` is checked against a
//!   subroutine type — the signature of a `define`, the parameter it is
//!   passed to, the handler position of a `prompt`.
//! * **A projection**, when a polymorphic value is applied or used where a
//!   known type is expected. Its binders are solved by matching: the
//!   parameter types against the arguments' types, and the result type
//!   against what is expected (Pierce & Turner's *local type inference*,
//!   specialised to FX's three kinds). A type binder must be solved, or it is
//!   an error to say so. An effect binder nothing constrains is `pure`. A
//!   region binder nothing constrains is a **fresh region**, one no other
//!   value is in: sound, since a region only partitions the store, and it is
//!   what makes `(car (cons 1 #t))` need no annotation.
//!
//! Everything inferred is what an explicit `proj` would have said, so the
//! rules of the kernel — masking included — apply unchanged afterwards.

use crate::ast::{Atom, Conv, D, DVar, Effect, Exp, ExpId, Kind, Region, Size, Ty, TyId};
use fixpt_read::Sym;
use crate::check::Checker;
use crate::error::{FxError, R};
use std::collections::{HashMap, HashSet};

/// An argument already synthesised: its type and effect.
type Synthesised = Option<(TyId, Effect)>;

/// The solution so far for a projection's binders.
struct Unknowns {
    kinds: Vec<(DVar, Kind)>,
    solved: HashMap<DVar, D>,
}

impl Unknowns {
    fn is_unknown(&self, v: DVar) -> bool {
        self.kinds.iter().any(|(u, _)| *u == v)
    }
}

impl Checker {
    // ----------------------------------------------------------- check mode

    /// Check `e` against `expected`, returning its effect.
    pub fn check(&mut self, e: ExpId, expected: TyId) -> R<Effect> {
        if self.holes.is_some() {
            self.at_hole(e, Some(expected))?;
        }
        let eff = self.check_node(e, expected)?;
        let eff = self.frozen(e, eff)?;
        self.facts.effects.insert(e, eff.clone());
        self.kill_paths(&eff);
        Ok(eff)
    }

    /// Whether `t` is `false`, or a union with it.
    fn false_expected(&self, t: TyId) -> bool {
        let is = |c: &Self, t: TyId| matches!(c.arena.get(c.arena.resolve(t)), Ty::False);
        match self.arena.get(self.arena.resolve(t)) {
            Ty::Union(ms) => ms.iter().any(|m| is(self, *m)),
            _ => is(self, t),
        }
    }

    fn check_node(&mut self, e: ExpId, expected: TyId) -> R<Effect> {
        let span = self.arena.span_of(e);
        let expected_ty = self.arena.get(expected).clone();
        match self.arena.exp_at(e).clone() {
            // `#f` where `false` is expected, or a union with it.
            Exp::Bool(false) if self.false_expected(expected) => Ok(Effect::pure()),
            // Against a `poly` type, anything but a `plambda` (or a `let`,
            // below, which passes the `poly` to its body) is checked with
            // the binders held abstract, as though it were wrapped in a
            // `plambda` binding them — so it must be pure, as a `plambda`
            // body must.
            _ if matches!(expected_ty, Ty::Poly { .. }) && !matches!(self.arena.exp_at(e), Exp::PLambda { .. } | Exp::Let { .. }) => {
                let Ty::Poly { body, .. } = expected_ty else { unreachable!() };
                let eff = self.check(e, body)?;
                if !self.generalizable(e, &eff) {
                    return Err(FxError::at(span, format!("a polymorphic value must be pure, and this has {}", self.show_effect(&eff))));
                }
                Ok(eff)
            }
            // A `plambda` against a `poly` of the same binders: the body is
            // checked against the `poly`'s body, its binders renamed to the
            // `plambda`'s, so what the signature says reaches inside.
            Exp::PLambda { binders, body }
                if matches!(&expected_ty, Ty::Poly { binders: bs, .. } if bs.len() == binders.len()
                    && bs.iter().zip(&binders).all(|((_, a), (_, b))| a == b)) =>
            {
                let Ty::Poly { binders: bs, body: want } = expected_ty else { unreachable!() };
                let map: HashMap<DVar, D> = bs
                    .iter()
                    .zip(&binders)
                    .map(|((vb, k), (va, _))| {
                        let d = match k {
                            Kind::Region | Kind::Place => D::Region(Region::Var(*va)),
                            Kind::Effect => D::Effect(Effect::atom(Atom::Var(*va))),
                            Kind::Type | Kind::Data => D::Type(self.arena.ty(Ty::Var(*va))),
                            Kind::Size => D::Size(Size::var(*va)),
                            Kind::Conv => D::Conv(crate::ast::Conv::Var(*va)),
                            Kind::Arrow(_) => D::Fun(self.arena.ty(Ty::Var(*va))),
                        };
                        (*vb, d)
                    })
                    .collect();
                let want = self.subst(want, &map);
                let eff = self.check(body, want)?;
                if !self.generalizable(body, &eff) {
                    return Err(FxError::at(span, format!("a `plambda` body must be pure, and this one has {}", self.show_effect(&eff))));
                }
                Ok(eff)
            }
            Exp::Lambda { params, .. } if expected_ty.as_subr().is_some() => {
                let (_, want, result) = expected_ty.as_subr().expect("a subroutine");
                if want.len() != params.len() {
                    return Err(FxError::at(span, format!("a subroutine of {} parameter(s) is expected, and this `lambda` has {}", want.len(), params.len())));
                }
                let (t, eff) = self.synth_lambda_as(e, Some(&want), Some(result))?;
                self.expect(e, t, expected)?;
                Ok(eff)
            }
            Exp::Lambda { params, .. } if params.iter().any(|(_, t)| t.is_none()) => {
                Err(FxError::at(span, format!("a `lambda` cannot be a {}", self.show_ty(expected))))
            }
            Exp::RLambda { region, lambda } if expected_ty.as_subr().is_some() => {
                let (t, eff) = self.synth_rlambda(e, region, lambda, Some(expected))?;
                self.expect(e, t, expected)?;
                Ok(eff)
            }
            Exp::App { fun, args } => {
                let (t, eff) = self.synth_app(e, fun, &args, Some(expected))?;
                self.expect(e, t, expected)?;
                Ok(eff)
            }
            Exp::Bloblet { op, args } => {
                let (t, eff) = self.synth_bloblet(e, op, &args, Some(expected))?;
                self.expect(e, t, expected)?;
                Ok(eff)
            }
            Exp::TagCase { scrutinee, arms, els } => Ok(self.synth_tagcase(e, scrutinee, &arms, &els, Some(expected))?.1),
            // A product checked against a product type of the same labels,
            // and a sum against a sum with its tag: the parts are checked
            // against theirs, so their lambdas and projections are inferred.
            Exp::Product(fields)
                if matches!(&expected_ty, Ty::Product(fs) if fs.len() == fields.len()
                    && fs.iter().zip(&fields).all(|((a, _), (b, _))| a == b)) =>
            {
                let Ty::Product(fs) = expected_ty else { unreachable!() };
                let mut eff = Effect::pure();
                for ((_, x), (_, t)) in fields.iter().zip(&fs) {
                    eff = eff.union(&self.check(*x, *t)?);
                }
                Ok(self.mask(e, &eff, expected))
            }
            Exp::Sum(tag, x) if matches!(&expected_ty, Ty::Sum(vs) if vs.iter().any(|(l, _)| *l == tag)) => {
                let Ty::Sum(vs) = expected_ty else { unreachable!() };
                let t = vs.iter().find(|(l, _)| *l == tag).expect("matched").1;
                let eff = self.check(x, t)?;
                Ok(self.mask(e, &eff, expected))
            }
            // A natural literal is a `nat`, and a `(nat k)`.
            Exp::Int(k) if k >= 0 && matches!(&expected_ty, Ty::Nat(s) if self.size_le(&Size::lit(k), s)) => Ok(Effect::pure()),
            // A literal in an `i32`'s or a `u32`'s range is one.
            Exp::Int(k) if matches!(&expected_ty, Ty::Base(b) if crate::check::fixed_range(self.interner.name(*b)).is_some_and(|(lo, hi)| (lo..=hi).contains(&k))) => {
                Ok(Effect::pure())
            }
            // `nil` is a `nlist` of no elements, or of some.
            Exp::Var(s)
                if self.interner.name(s) == "nil"
                    && self.is_standard(s)
                    && matches!(&expected_ty, Ty::NList { size, .. } if matches!(size, Size::Finite) || self.size_eq(size, &Size::lit(0))) =>
            {
                Ok(Effect::pure())
            }
            // A standard polymorphic value through `#%fx` (`(with #%fx
            // nil)`), instantiated as the plain name is (`TODO.md` §46).
            Exp::With { module, body } if self.fx_poly(module, body).is_some() => {
                let t = self.fx_poly(module, body).expect("matched");
                let inst = self.instantiate_against(t, expected, span)?;
                self.expect(e, inst, expected)?;
                self.plain_fx(e);
                Ok(Effect::pure())
            }
            Exp::Var(s) if self.lookup(s).is_some_and(|t| matches!(self.arena.get(t), Ty::Poly { .. })) => {
                let t = self.lookup(s).expect("bound");
                let inst = self.instantiate_against(t, expected, span)?;
                self.expect(e, inst, expected)?;
                Ok(self.naming_effect(s, t))
            }
            Exp::If { test, then, els } => {
                let te = self.check(test, self.bool_ty())?;
                let certified = self.acyclic_test(test);
                self.certified.extend(certified);
                let lengths = self.length_test(test);
                self.certified_lengths.extend(lengths.clone());
                let nats = self.nat_test(test);
                self.certified_nats.extend(nats);
                let (yes, no) = self.test_facts(test);
                let (narrow_yes, narrow_no) = self.narrowings(test);
                let depth = self.size_facts.len();
                let narrowed = (self.narrowed.len(), self.path_narrowed.len());
                self.size_facts.extend(yes);
                self.push_narrowings(narrow_yes);
                let ae = self.check(then, expected);
                self.size_facts.truncate(depth);
                self.narrowed.truncate(narrowed.0);
                self.path_narrowed.truncate(narrowed.1);
                if certified.is_some() {
                    self.certified.pop();
                }
                if lengths.is_some() {
                    self.certified_lengths.pop();
                }
                if nats.is_some() {
                    self.certified_nats.pop();
                }
                let ae = ae?;
                self.size_facts.extend(no);
                self.push_narrowings(narrow_no);
                let be = self.check(els, expected);
                self.size_facts.truncate(depth);
                self.narrowed.truncate(narrowed.0);
                self.path_narrowed.truncate(narrowed.1);
                let be = be?;
                Ok(self.mask(e, &te.union(&ae).union(&be), expected))
            }
            Exp::Begin(items) => {
                let (last, init) = items.split_last().expect("a body is not empty");
                let mut eff = Effect::pure();
                for i in init {
                    eff = eff.union(&self.synth(*i)?.1);
                }
                eff = eff.union(&self.check(*last, expected)?);
                Ok(self.mask(e, &eff, expected))
            }
            // A `letrec`'s body, as a `let`'s, against what is expected.
            Exp::Letrec { bindings, body } => Ok(self.letrec(e, &bindings, body, Some(expected))?.1),
            Exp::Let { bindings, body } => {
                let mut eff = Effect::pure();
                let mut bound = Vec::new();
                // Where the bindings will be in `env`.
                let base = self.env.len();
                for (i, (n, init)) in bindings.iter().enumerate() {
                    let (t, ie) = self.synth(*init)?;
                    eff = eff.union(&ie);
                    if self.is_lambda(*init) {
                        self.known.insert((*n, base + i));
                    }
                    bound.push((*n, t));
                }
                let depth = self.env.len();
                let named = self.skolems.len();
                for (n, t) in bound {
                    let t = self.name_nat(n, t);
                    self.env.push((n, t));
                }
                let r = self.check(body, expected);
                self.truncate_env(depth);
                self.skolems.truncate(named);
                let eff = self.mask(e, &eff.union(&r?), expected);
                // A `let` whose value is polymorphic (a `plambda` under it,
                // say) must be pure, as a `plambda` body must.
                if matches!(expected_ty, Ty::Poly { .. }) && !self.generalizable(e, &eff) {
                    return Err(FxError::at(span, format!("a polymorphic value must be pure, and this has {}", self.show_effect(&eff))));
                }
                Ok(eff)
            }
            _ => {
                let (t, eff) = self.synth(e)?;
                self.expect(e, t, expected)?;
                Ok(eff)
            }
        }
    }

    /// `got ≤ want`, or an error at `e` saying so.
    pub(crate) fn expect(&mut self, e: ExpId, got: TyId, want: TyId) -> R<()> {
        if self.subtype(got, want) {
            return Ok(());
        }
        if let Some((c, n)) = self.conversion(got, want) {
            self.convert_at(e, c, n);
            return Ok(());
        }
        if let Some(at) = self.reshape(got, want) {
            self.facts.reshaped.insert(e, at);
            return Ok(());
        }
        Err(FxError::at(
            self.arena.span_of(e),
            format!("a {} is expected here, and this is a {}{}", self.show_ty(want), self.show_ty(got), self.effect_delta(got, want)),
        ))
    }

    /// The convention `want` asks of `got`, where a procedure differs from
    /// what is expected only in its convention, so that a conversion makes
    /// it one (`docs/research/native-conventions.md`); and its arity.
    fn conversion(&mut self, got: TyId, want: TyId) -> Option<(Conv, usize)> {
        let (g, w) = (self.arena.resolve(got), self.arena.resolve(want));
        let (Ty::Subr { conv: from, effect, params, result }, Ty::Subr { conv: to, .. }) = (self.arena.get(g).clone(), self.arena.get(w).clone()) else {
            return None;
        };
        if from == to {
            return None;
        }
        let n = params.len();
        let t = self.arena.ty(Ty::Subr { conv: to, effect, params, result });
        self.subtype(t, want).then_some((to, n))
    }

    /// A conversion of `e`'s procedure, of `arity` arguments, to `to`. To
    /// `fx` or to a convention binder it does nothing at run time; to
    /// `cellular` or `native` it is `%fx26-convert`, which gives the value
    /// if it is already one of those, and otherwise an adapter: a
    /// procedure of the convention asked for that calls it.
    pub(crate) fn convert_at(&mut self, e: ExpId, to: Conv, arity: usize) {
        self.facts.converted.insert(e, (to, arity));
    }

    // --------------------------------------------------------------- lambda

    /// A `lambda`'s type. `hint` supplies the types of parameters the
    /// program left out; without it, every parameter must have one.
    pub(crate) fn synth_lambda(&mut self, e: ExpId, hint: Option<&[TyId]>) -> R<(TyId, Effect)> {
        self.synth_lambda_as(e, hint, None)
    }

    /// The same, with the body checked against `result` when it is known.
    pub(crate) fn synth_lambda_as(&mut self, e: ExpId, hint: Option<&[TyId]>, result: Option<TyId>) -> R<(TyId, Effect)> {
        let Exp::Lambda { params, body } = self.arena.exp_at(e).clone() else { unreachable!() };
        let mut typed = Vec::new();
        for (i, (n, t)) in params.iter().enumerate() {
            match (t, hint.and_then(|h| h.get(i))) {
                (Some(t), _) => typed.push((*n, *t)),
                (None, Some(h)) => typed.push((*n, *h)),
                (None, None) => {
                    return Err(FxError::at(
                        self.arena.span_of(e),
                        format!(
                            "the type of parameter `{}` cannot be known here: write `({} type)`, or check the `lambda` against a type",
                            self.interner.name(*n),
                            self.interner.name(*n)
                        ),
                    ));
                }
            }
        }
        // Bound in order: a parameter's type may name a module in scope, or
        // an earlier parameter (`(select m t)`), a dependent procedure
        // (`first-class-modules.md`, M5). What it names of an earlier one is,
        // in the procedure's type, `(select $k t)`; a type told it (`hint`,
        // `result`) says it so, and is given the earlier parameter's.
        let span = self.arena.span_of(e);
        let names: Vec<Sym> = params.iter().map(|(n, _)| *n).collect();
        let depth = self.env.len();
        let named = self.skolems.len();
        let (mut given, mut back): (HashMap<(usize, Sym), TyId>, HashMap<DVar, D>) = (HashMap::new(), HashMap::new());
        for (j, (n, t)) in typed.iter_mut().enumerate() {
            let resolved = match self.resolve_selects_outside(*t, &names[j..], span) {
                Ok(r) => r,
                Err(err) => {
                    self.truncate_env(depth);
                    self.skolems.truncate(named);
                    return Err(err);
                }
            };
            let resolved = self.instantiate_params(resolved, &given);
            let bound = self.name_nat(*n, resolved);
            self.env.push((*n, bound));
            *t = if back.is_empty() { resolved } else { self.subst(resolved, &back) };
            if let Ty::Module { abs, .. } = self.arena.get(self.arena.resolve(bound)).clone() {
                for (a, w) in abs {
                    given.insert((j, a), self.arena.ty(Ty::Var(w)));
                    back.insert(w, D::Type(self.arena.ty(Ty::ParamSel(j, a))));
                }
            }
        }
        let result = result.map(|r| self.instantiate_params(r, &given));
        // The body's effect is masked *with the parameters in scope*: they
        // are free in the body, so what reaches them stays.
        // A closure may run later, after any write: no path's fact holds in
        // its body (`Checker::path_fact`).
        self.closure_depth += 1;
        let r = match result {
            Some(want) => self.check(body, want).map(|eff| (want, self.mask(body, &eff, want))),
            None => self.synth(body).map(|(t, eff)| (t, self.mask(body, &eff, t))),
        };
        self.closure_depth -= 1;
        self.truncate_env(depth);
        let span = self.arena.span_of(e);
        // What the result says of a parameter's types, it says as the
        // procedure's type does.
        let r = r.map(|(t, latent)| (if back.is_empty() { t } else { self.subst(t, &back) }, latent));
        let r = r.and_then(|(t, latent)| Ok((self.forget_nats(named, t, span)?, latent)));
        self.skolems.truncate(named);
        let (result, latent) = r?;
        let t = self.arena.ty(Ty::Subr { conv: self.conv_default, effect: latent, params: typed.iter().map(|(_, t)| *t).collect(), result });
        Ok((t, Effect::pure()))
    }

    fn unannotated_lambda(&self, e: ExpId) -> bool {
        matches!(self.arena.exp_at(e), Exp::Lambda { params, .. } if params.iter().any(|(_, t)| t.is_none()))
    }

    /// An argument that is better told what it is than asked: a `lambda`
    /// missing parameter types, or a thunk, whose body may need to know the
    /// result it must produce.
    fn needs_telling(&self, e: ExpId) -> bool {
        self.unannotated_lambda(e) || matches!(self.arena.exp_at(e), Exp::Lambda { params, .. } if params.is_empty())
    }

    // ----------------------------------------------------------- application

    /// An application, with the operator instantiated first if it is
    /// polymorphic. `expected` is the type the application should have, when
    /// that is known; it helps solve the operator's binders.
    pub(crate) fn synth_app(&mut self, e: ExpId, fun: ExpId, args: &[ExpId], expected: Option<TyId>) -> R<(TyId, Effect)> {
        let (t, eff) = self.synth_app_of(e, fun, args, expected)?;
        // A path a fact in force narrows (`(car x)` …), its type there.
        let t = self.path_typed(e, t);
        // A test's call is a `bool`: what the test's type says it proves is
        // of these arguments, here (`Checker::narrowings`), and nowhere else.
        let t = match self.arena.get(self.arena.resolve(t)) {
            Ty::Proving { .. } => self.bool_,
            _ => t,
        };
        Ok((t, eff))
    }

    fn synth_app_of(&mut self, e: ExpId, fun: ExpId, args: &[ExpId], expected: Option<TyId>) -> R<(TyId, Effect)> {
        // The operator `(with #%fx n)` noted plain where it is, by this rule
        // whether or not the rules below look at the operator itself.
        let mut op = fun;
        while let Exp::Proj { body, .. } | Exp::The { exp: body, .. } = self.arena.exp_at(op) {
            op = *body;
        }
        self.plain_fx(op);
        // `(certify-length v k)`: `v`'s value as a `(nlist T k)`, where
        // `length-is?` has just found it so; nowhere else.
        if let Some(op) = self.standard_ref(fun)
            && self.interner.name(op) == "certify-length"
        {
            let span = self.arena.span_of(e);
            let found = match &args[..] {
                [a, n] => self.length_arg(*a, *n),
                _ => None,
            };
            let Some((_, _, k)) = found.filter(|f| self.certified_lengths.contains(f)) else {
                return Err(FxError::at(span, "`certify-length` takes only a variable and a length `length-is?` has just confirmed"));
            };
            let (t, eff) = self.synth(args[0])?;
            let t = self.arena.resolve(t);
            let (elem, region) = match self.arena.get(t).clone() {
                Ty::Pair(elem, tail, r, _) if self.arena.resolve(tail) == t && r.is_frozen() => (elem, r),
                Ty::NList { elem, region, .. } => (elem, region),
                _ => return Err(FxError::at(span, format!("`certify-length` takes a frozen list, and this is a {}", self.show_ty(t)))),
            };
            let region = match region {
                Region::Frozen(p, _) => Region::Frozen(p, true),
                r => r,
            };
            return Ok((self.arena.ty(Ty::NList { elem, size: k, region }), eff));
        }
        // `+` and `-` of naturals: a natural, of a size when both are known.
        if let Some(op) = self.standard_ref(fun)
            && let name @ ("+" | "-") = self.interner.name(op)
            && let [a, b] = args
        {
            let name = name.to_string();
            // Still the standard operation, for the lowering to integrate.
            self.facts.standard_operator.insert(e, op);
            let mut eff = Effect::pure();
            let mut sizes = Vec::new();
            for x in [*a, *b] {
                // Only what has a type of its own is asked for it; anything
                // else is told it is an int, as for any call.
                if !self.natural_by_itself(x) {
                    eff = eff.union(&self.check(x, self.int)?);
                    sizes.push(None);
                    continue;
                }
                let (t, xe) = self.synth(x)?;
                self.expect(x, t, self.int)?;
                eff = eff.union(&xe);
                sizes.push(match (self.arena.exp_at(x), self.arena.get(self.arena.resolve(t))) {
                    (Exp::Int(k), _) if *k >= 0 => Some(Size::lit(*k)),
                    (_, Ty::Nat(s)) => Some(s.clone()),
                    _ => None,
                });
            }
            let t = match (&sizes[0], &sizes[1]) {
                (Some(x), Some(y)) => self.nat_arith(&name, x, y).map(|s| self.arena.ty(Ty::Nat(s))),
                _ => None,
            };
            return Ok((t.unwrap_or(self.int), eff));
        }
        // `cons` onto a `nlist`: one more element. Where a `nlist` is expected,
        // the tail is checked as one shorter; otherwise, a tail that is a
        // variable of `nlist` type gives a `nlist` one longer.
        if let Some(op) = self.standard_ref(fun)
            && self.interner.name(op) == "cons"
            && let [x, tail] = args
        {
            let want = expected.map(|t| self.arena.get(self.arena.resolve(t)).clone());
            if let Some(Ty::NList { elem, size, region }) = want
                && (matches!(size, Size::Finite) || self.size_nonneg(&size.plus(-1)))
            {
                let tail_ty = self.arena.ty(Ty::NList { elem, size: size.plus(-1), region });
                let xe = self.check(*x, elem)?;
                let te = self.check(*tail, tail_ty)?;
                return Ok((expected.expect("an nlist"), xe.union(&te)));
            }
            if let Exp::Var(v) = self.arena.exp_at(*tail)
                && let Some(t) = self.lookup(*v)
                && let Ty::NList { elem, size, region } = self.arena.get(self.arena.resolve(t)).clone()
            {
                let xe = self.check(*x, elem)?;
                let (_, te) = self.synth(*tail)?;
                let t = self.arena.ty(Ty::NList { elem, size: size.plus(1), region });
                return Ok((t, xe.union(&te)));
            }
        }
        // `(certify-nat v)`: `v`'s value as a `nat`, where `nat?` has just
        // found `v` no less than 0; nowhere else.
        if let Some(op) = self.standard_ref(fun)
            && self.interner.name(op) == "certify-nat"
        {
            let span = self.arena.span_of(e);
            let v = match &args[..] {
                [a] => match self.arena.exp_at(*a) {
                    Exp::Var(v) => self.env.iter().rposition(|(n, _)| n == v).map(|i| (*v, i)),
                    _ => None,
                },
                _ => None,
            };
            if !v.is_some_and(|v| self.certified_nats.contains(&v)) {
                return Err(FxError::at(span, "`certify-nat` takes only a variable `nat?` has just found no less than 0"));
            }
            let (t, eff) = self.synth(args[0])?;
            self.expect(args[0], t, self.int)?;
            return Ok((self.arena.ty(Ty::Nat(Size::Finite)), eff));
        }
        // `(certify-acyclic v)`: `v`'s value at `acyclic`, where `acyclic?`
        // has just found `v` acyclic; nowhere else.
        if let Some(op) = self.standard_ref(fun)
            && self.interner.name(op) == "certify-acyclic"
        {
            let span = self.arena.span_of(e);
            let v = match &args[..] {
                [a] => match self.arena.exp_at(*a) {
                    Exp::Var(v) => self.env.iter().rposition(|(n, _)| n == v).map(|i| (*v, i)),
                    _ => None,
                },
                _ => None,
            };
            if !v.is_some_and(|v| self.certified.contains(&v)) {
                return Err(FxError::at(span, "`certify-acyclic` takes only a variable `acyclic?` has just found acyclic"));
            }
            let (t, eff) = self.synth(args[0])?;
            if !self.is_data(t) {
                return Err(FxError::at(span, format!("`certify-acyclic` takes data, and a {} is not data", self.show_ty(t))));
            }
            return Ok((self.finitized(t), eff));
        }
        let span = self.arena.span_of(e);
        if let Some(s) = self.standard_ref(fun) {
            self.facts.standard_operator.insert(e, s);
        }
        let mut op = fun;
        while let Exp::Proj { body, .. } | Exp::The { exp: body, .. } = self.arena.exp_at(op) {
            op = *body;
        }
        let outer = self.operator_at.replace(op);
        let synthesised = self.synth(fun);
        self.operator_at = outer;
        let (mut ft, fe) = synthesised?;
        let mut done: Vec<Synthesised> = vec![None; args.len()];
        if matches!(self.arena.get(ft), Ty::Poly { .. }) {
            let (inst, cached) = self.instantiate(e, ft, args, expected, span)?;
            self.no_knot(inst, span)?;
            ft = inst;
            done = cached;
        }
        let callee = self.arena.get(ft).clone();
        // A `vsubr` (generative type 0): any number of arguments, each of
        // its element type.
        if let Ty::Named { which: 0, args: ds } = &callee
            && let [D::Effect(latent), D::Type(elem), D::Type(result)] = &ds[..]
        {
            let (latent, elem, result) = (latent.clone(), *elem, *result);
            let mut effect = fe;
            for (i, a) in args.iter().enumerate() {
                effect = effect.union(&self.check(*a, elem).map_err(|err| self.as_argument(err, *a, i))?);
            }
            let mut effect = effect.union(&latent);
            if self.may_spin(fun, ft, args) {
                effect.0.insert(Atom::Spin);
            }
            let effect = self.mask(e, &effect, result);
            return Ok((result, effect));
        }
        let Some((latent, params, result)) = callee.as_subr() else {
            return Err(FxError::at(span, format!("not a subroutine: {}", self.show_ty(ft))));
        };
        // A dependent procedure: its types given the modules its arguments
        // name.
        let (params, result) = self.dependent_args(&params, result, args, span)?;
        // `apply` of a list at `acyclic`: no copy.
        if matches!(self.facts.standard_operator.get(&e), Some(s) if self.interner.name(*s) == "apply")
            && let [_, list] = params[..]
            && matches!(self.arena.get(self.arena.resolve(list)), Ty::Pair(_, _, Region::Frozen(_, true), _))
        {
            self.facts.apply_shares.insert(e);
        }
        // A procedure of the other convention is called as through `fx`
        // (`native ≤ fx`, `cellular ≤ fx`): every call looks at its
        // callee's kind, as a call through `fx` does.
        if params.len() != args.len() {
            return Err(FxError::at(span, format!("expected {} argument(s), got {}", params.len(), args.len())));
        }
        let mut effect = fe;
        for (i, (a, p)) in args.iter().zip(&params).enumerate() {
            let eff = match done[i].take() {
                Some((t, eff)) => {
                    if !self.subtype(t, *p) {
                        let Some((c, n)) = self.conversion(t, *p) else {
                            return Err(FxError::at(
                                self.arena.span_of(*a),
                                format!("argument {} is a {}, where a {} is expected", i + 1, self.show_ty(t), self.show_ty(*p)),
                            ));
                        };
                        self.convert_at(*a, c, n);
                    }
                    eff
                }
                None => self.check(*a, *p).map_err(|err| self.as_argument(err, *a, i))?,
            };
            effect = effect.union(&eff);
        }
        let mut effect = effect.union(&latent);
        if self.may_spin(fun, ft, args) {
            effect.0.insert(Atom::Spin);
        }
        let effect = self.mask(e, &effect, result);
        Ok((result, effect))
    }

    /// Whether a call of `fun` (instantiated to `ft`) may run for an
    /// unbounded time beyond what its latent effect says
    /// (`docs/research/type-and-effect-directions.md`, R6):
    /// - a call, in a recursive group's lambdas, of the group, whose types
    ///   say `spin` only once checked;
    /// - a call through a recursive type of anything but known code: a
    ///   procedure can be given itself, and loop with no store at all.
    ///
    /// A knot tied through the store needs nothing here: a procedure kept
    /// in storage whose latent effect reads that storage must say `spin`
    /// (`no_knot`), so latent effects can be trusted.
    fn may_spin(&self, fun: ExpId, ft: TyId, args: &[ExpId]) -> bool {
        let binding = self.callee_binding(fun);
        let mut op = fun;
        while let Exp::Proj { body, .. } | Exp::The { exp: body, .. } = self.arena.exp_at(op) {
            op = *body;
        }
        let standard = self.standard_ref(op);
        // A continuation called after `cwcc` has returned comes back to it
        // again, as often as it is called: recursion with no procedure at
        // all (`docs/research/soundness-findings.md`, F3). Only one that
        // cannot outlive the call, so can only leave it, needs no `spin`.
        // `cwcc` is named nowhere else (F15), so every call of it is here.
        if standard.is_some_and(|s| self.interner.name(s) == "cwcc") {
            // And the receiver must capture no continuation: one captured
            // inside it could hold a call of `k`, and be run after `cwcc`
            // has returned (F9). A capture shows as a `comefrom` in the
            // receiver's latent effect, what `cwcc`'s `e` was solved to.
            let captures = self.arena.get(ft).as_subr().and_then(|(_, ps, _)| {
                let p = *ps.first()?;
                self.arena.get(self.arena.resolve(p)).as_subr().map(|(e, _, _)| e.0.iter().any(|a| matches!(a, Atom::Comefrom(_))))
            });
            return captures != Some(false) || !matches!(args, [r] if self.escape_only(*r));
        }
        if let Some(b) = binding {
            if self.recursive.contains(&b) {
                return true;
            }
            let at = self.env.iter().rposition(|(n, _)| *n == b.0);
            if at.is_some_and(|i| self.known.contains(&(b.0, i))) || self.is_standard(b.0) {
                return false;
            }
        }
        if standard.is_some() {
            return false;
        }
        // A `lambda` applied where it is written is known code too.
        let mut f = fun;
        while let Exp::Proj { body, .. } | Exp::The { exp: body, .. } = self.arena.exp_at(f) {
            f = *body;
        }
        !self.is_lambda(f) && self.cyclic(ft)
    }

    /// Whether `receiver`, given to `cwcc`, is a `lambda` whose continuation
    /// can only be called while `cwcc` runs: its parameter is named only as
    /// the operator of calls in its body, outside any `lambda` (which could
    /// be called later) and any prompt (whose captures could be composed
    /// later).
    fn escape_only(&self, receiver: ExpId) -> bool {
        let mut r = receiver;
        while let Exp::The { exp, .. } = self.arena.exp_at(r) {
            r = *exp;
        }
        match self.arena.exp_at(r) {
            Exp::Lambda { params, body } if params.len() == 1 => self.only_called(*body, params[0].0),
            _ => false,
        }
    }

    /// Whether `k` is named in `e` only as the operator of calls, evaluated
    /// as `e` is.
    fn only_called(&self, e: ExpId, k: Sym) -> bool {
        let all = |xs: Vec<ExpId>| xs.into_iter().all(|x| self.only_called(x, k));
        match self.arena.exp_at(e).clone() {
            Exp::Var(s) => s != k,
            Exp::App { fun, args } => {
                (matches!(self.arena.exp_at(fun), Exp::Var(s) if *s == k) || self.only_called(fun, k)) && all(args)
            }
            Exp::Lambda { .. } | Exp::PLambda { .. } | Exp::RLambda { .. } | Exp::Letrec { .. } | Exp::Prompt { .. } | Exp::Module(_) | Exp::With { .. } => {
                !self.free_vars(e).contains(&k)
            }
            Exp::Let { bindings, body } => {
                all(bindings.iter().map(|(_, x)| *x).collect()) && (bindings.iter().any(|(n, _)| *n == k) || self.only_called(body, k))
            }
            Exp::LetRegion { region, body, .. } => self.arena.dvar_name(region) == k || self.only_called(body, k),
            Exp::TagCase { scrutinee, arms, els } => {
                self.only_called(scrutinee, k)
                    && arms.iter().all(|arm| arm.names().contains(&k) || self.only_called(arm.body, k))
                    && els.is_none_or(|(y, body)| y == k || self.only_called(body, k))
            }
            Exp::Proj { body, .. } | Exp::The { exp: body, .. } | Exp::Convention { exp: body, .. } | Exp::Extract(body, _) | Exp::Sum(_, body) => self.only_called(body, k),
            Exp::If { test, then, els } => all(vec![test, then, els]),
            Exp::Begin(items) | Exp::Bloblet { args: items, .. } => all(items),
            Exp::Product(fields) => all(fields.into_iter().map(|(_, x)| x).collect()),
            Exp::Int(_) | Exp::Bool(_) | Exp::Str(_) | Exp::Char(_) | Exp::Float(_) | Exp::Symbol(_) | Exp::Unit => true,
        }
    }

    /// The binding `f` names, under any projections and ascriptions: its
    /// name and type, if it is a variable.
    pub(crate) fn callee_binding(&self, mut f: ExpId) -> Option<(Sym, TyId)> {
        while let Exp::Proj { body, .. } | Exp::The { exp: body, .. } = self.arena.exp_at(f) {
            f = *body;
        }
        match self.arena.exp_at(f) {
            Exp::Var(s) => self.lookup(*s).map(|t| (*s, t)),
            _ => None,
        }
    }

    /// Whether a procedure of type `t` could be given itself: a cycle in `t`
    /// runs through a parameter of a procedure (or the argument of a
    /// continuation). A type that is merely recursive, as a list is, does not
    /// let anything loop.
    pub(crate) fn cyclic(&self, t: TyId) -> bool {
        // `path`: the nodes on the way down, each with whether it was
        // reached through a parameter.
        fn walk(c: &Checker, t: TyId, by_param: bool, path: &mut Vec<(TyId, bool)>) -> bool {
            let t = c.arena.resolve(t);
            if let Some(i) = path.iter().position(|(x, _)| *x == t) {
                return by_param || path[i + 1..].iter().any(|(_, p)| *p);
            }
            // Too deep to follow: say it may loop, as the cautious answer
            // (`docs/research/soundness-findings.md`, F5).
            if path.len() > 64 {
                return true;
            }
            path.push((t, by_param));
            let kids: Vec<(TyId, bool)> = match c.arena.get(t) {
                Ty::Subr { params, result, .. } => params.iter().map(|p| (*p, true)).chain([(*result, false)]).collect(),
                Ty::Composable { arg, answer, .. } => vec![(*arg, true), (*answer, false)],
                Ty::PromptTag { answer, payload, .. } => vec![(*answer, false), (*payload, false)],
                Ty::Poly { body, .. } => vec![(*body, false)],
                Ty::Ref(a, _) | Ty::Array(a, _) | Ty::ICell(a, _) | Ty::MarkKey(a, _) => vec![(*a, false)],
                Ty::Pair(a, b, _, _) => vec![(*a, false), (*b, false)],
                Ty::Bloblet { fields, .. } => fields.iter().map(|f| (*f, false)).collect(),
                Ty::Product(ps) | Ty::Sum(ps) => ps.iter().map(|(_, t)| (*t, false)).collect(),
                Ty::Union(ms) => ms.iter().map(|t| (*t, false)).collect(),
                Ty::NList { elem, .. } => vec![(*elem, false)],
                // Through its representation; what it was given, cautiously,
                // as if taken as a parameter.
                Ty::Named { which, args } => [(c.generatives[*which as usize].rep, false)]
                    .into_iter()
                    .chain(args.iter().flat_map(|d| c.d_types(d)).map(|x| (x, true)))
                    .collect(),
                // A description function applied, unseen: what it was
                // given, cautiously, as if taken as a parameter.
                Ty::App { args, .. } => args.iter().flat_map(|d| c.d_types(d)).map(|x| (x, true)).collect(),
                _ => vec![],
            };
            let r = kids.into_iter().any(|(k, p)| walk(c, k, p, path));
            path.pop();
            r
        }
        walk(self, t, false, &mut Vec::new())
    }

    /// An argument that failed to check is reported as that argument.
    fn as_argument(&self, err: FxError, a: ExpId, i: usize) -> FxError {
        // One `a ` only: the type may itself be called `a`.
        if err.span == self.arena.span_of(a)
            && let Some((want, got, delta)) = crate::check::expected_and_found(&err.message)
        {
            return FxError::at(err.span, format!("argument {} is a {got}, where a {want} is expected{delta}", i + 1));
        }
        err
    }

    // --------------------------------------------------------- instantiation

    /// The binders of `t`, through every nested `poly`, and the type under
    /// them all.
    pub(crate) fn binders_of(&self, t: TyId) -> (Vec<(DVar, Kind)>, TyId) {
        let mut all = Vec::new();
        let mut t = self.arena.resolve(t);
        while let Ty::Poly { binders, body } = self.arena.get(t).clone() {
            all.extend(binders);
            t = self.arena.resolve(body);
        }
        (all, t)
    }

    /// Instantiate the polymorphic operator type `ft` for a call with `args`,
    /// synthesising the arguments on the way. Returns the instantiated type
    /// and, for each argument already synthesised, its type and effect.
    fn instantiate(
        &mut self,
        e: ExpId,
        ft: TyId,
        args: &[ExpId],
        expected: Option<TyId>,
        span: fixpt_read::Span,
    ) -> R<(TyId, Vec<Synthesised>)> {
        let (kinds, inner) = self.binders_of(ft);
        // A `vsubr` (a standard `list`): a subroutine of as many parameters
        // as there are arguments, each of its argument type.
        let callee = match self.arena.get(inner) {
            Ty::Named { which: 0, args: ds } => match &ds[..] {
                [D::Effect(e), D::Type(elem), D::Type(r)] => Some((e.clone(), vec![*elem; args.len()], *r)),
                _ => None,
            },
            t => t.as_subr(),
        };
        let Some((_, params, result)) = callee else {
            return Err(FxError::at(span, format!("not a subroutine, even once projected: {}", self.show_ty(ft))));
        };
        if params.len() != args.len() {
            return Err(FxError::at(span, format!("expected {} argument(s), got {}", params.len(), args.len())));
        }
        let mut u = Unknowns { kinds, solved: HashMap::new() };
        let mut done: Vec<Synthesised> = vec![None; args.len()];
        // What the whole is expected to be, first: it often fixes enough that
        // an argument can be told its type rather than asked — which is what
        // puts every pair of `(cons a (cons b nil))` in the expected region.
        if let Some(want) = expected {
            self.unify(result, want, &mut u, &mut HashSet::new());
        }
        // What the arguments are, except the ones that need to be told.
        for (i, a) in args.iter().enumerate() {
            if self.needs_telling(*a) {
                continue;
            }
            let p = self.subst(params[i], &u.solved);
            if !self.mentions_any_unknown(p, &u) {
                let eff = self.check(*a, p)?;
                done[i] = Some((p, eff));
                continue;
            }
            let (t, eff) = self.synth(*a)?;
            if matches!(self.arena.get(t), Ty::Poly { .. }) {
                continue;
            }
            self.unify(params[i], t, &mut u, &mut HashSet::new());
            done[i] = Some((t, eff));
        }
        self.partial_pair_argument(e, &params, &mut done, &mut u);
        // A shape conflict is the error to report, before any binder is
        // found unsolved (`DONE.md` §20): the result against what the
        // context expects, which `unify` only uses as a hint, then each
        // argument found so far against its parameter.
        if let Some(want) = expected
            && self.result_misfits(want, result)
        {
            let map = self.partial_map(&u);
            let got = self.subst(result, &map);
            let got = self.show_open(got, &u);
            return Err(FxError::at(span, format!("this is a {got}, where a {} is expected", self.show_ty(want))));
        }
        self.shape_errors(args, &params, &done, &u)?;
        // The arguments that needed telling: each is checked against its
        // parameter as solved so far, and what it turns out to be solves more.
        for (i, a) in args.iter().enumerate() {
            if done[i].is_some() {
                continue;
            }
            self.default_regions(&mut u);
            let map = self.partial_map(&u);
            let p = self.subst(params[i], &map);
            let not_known = |c: &Checker, t: TyId| {
                FxError::at(
                    c.arena.span_of(*a),
                    format!(
                        "argument {} must be a {}, which is not yet known here; give the other arguments first, or `proj` the operator",
                        i + 1,
                        c.show_ty(t)
                    ),
                )
            };
            if self.needs_telling(*a) {
                // The parameter types must be known; the result helps if it
                // is, and otherwise the body says what it is.
                let Some((_, ps, res)) = self.arena.get(p).as_subr() else {
                    // A thunk has no parameters to be told: told nothing, it
                    // says what it is, as any argument does.
                    if !self.unannotated_lambda(*a) {
                        let (t, eff) = self.synth(*a)?;
                        self.unify(params[i], t, &mut u, &mut HashSet::new());
                        done[i] = Some((t, eff));
                        continue;
                    }
                    return Err(not_known(self, p));
                };
                if ps.iter().any(|t| self.mentions_unknown_type(*t, &u)) {
                    return Err(not_known(self, p));
                }
                let res = (!self.mentions_unknown_type(res, &u)).then_some(res);
                let (t, eff) = self.synth_lambda_as(*a, Some(&ps), res)?;
                self.unify(params[i], t, &mut u, &mut HashSet::new());
                done[i] = Some((t, eff));
            } else if self.mentions_unknown_type(p, &u)
                && let Exp::Var(s) = *self.arena.exp_at(*a)
                && let Some(t) = self.lookup(s).filter(|t| self.list_of_any(*t))
            {
                // `nil` where nothing yet says which list: the type `nil`
                // (`TODO.md` §48), heard last, after what the context
                // expects and every other argument.
                let nil = self.arena.ty(Ty::Nil);
                self.unify(params[i], nil, &mut u, &mut HashSet::new());
                if self.mentions_unknown_type(params[i], &u) {
                    return Err(not_known(self, p));
                }
                done[i] = Some((nil, self.naming_effect(s, t)));
            } else if self.mentions_unknown_type(p, &u) {
                return Err(not_known(self, p));
            } else if let Exp::Var(s) = *self.arena.exp_at(*a)
                && let Some(t) = self.lookup(s).filter(|t| matches!(self.arena.get(*t), Ty::Poly { .. }))
            {
                // A variable of a polymorphic type: instantiated at the
                // parameter, and what it turns out to be solves more
                // (`(apply list xs)`: `apply`'s effect).
                let inst = self.instantiate_against(t, p, self.arena.span_of(*a))?;
                self.unify(params[i], inst, &mut u, &mut HashSet::new());
                done[i] = Some((inst, self.naming_effect(s, t)));
            } else {
                let eff = self.check(*a, p)?;
                done[i] = Some((p, eff));
            }
        }
        // An argument of the wrong shape altogether is the error to report,
        // before any binder it left unsolved.
        self.shape_errors(args, &params, &done, &u)?;
        self.default_regions(&mut u);
        if expected.is_none() {
            self.widen_nil_tail(result, &mut u);
        }
        let map = self.finish(&u, span, ft)?;
        self.check_bounds(&u.kinds, &map, span)?;
        self.check_finite_sizes(&u.kinds, &map, inner, span)?;
        let inst = self.subst(inner, &map);
        Ok((inst, done))
    }

    /// What argument `index` of `op` must be, given some of the others: the
    /// operator's parameter, with whatever the given arguments solve filled
    /// in. For the REPL's hint, so nothing here is an error.
    pub(crate) fn argument_want(&mut self, op: ExpId, given: &[(usize, ExpId)], index: usize) -> Option<TyId> {
        let (ft, _) = self.synth(op).ok()?;
        let (kinds, inner) = self.binders_of(ft);
        let (_, params, _) = self.arena.get(inner).as_subr()?;
        let want = *params.get(index)?;
        let mut u = Unknowns { kinds, solved: HashMap::new() };
        for (i, a) in given {
            let Some(p) = params.get(*i) else { continue };
            if let Ok((t, _)) = self.synth(*a) {
                self.unify(*p, t, &mut u, &mut HashSet::new());
            }
        }
        Some(self.subst(want, &u.solved))
    }

    /// Instantiate a polymorphic value used, unapplied, where `expected` is
    /// wanted.
    pub(crate) fn instantiate_against(&mut self, t: TyId, expected: TyId, span: fixpt_read::Span) -> R<TyId> {
        // A list of any elements (`nil`, `no-pair`) is the empty list, so
        // `nil` where that is wanted, or a pair that may be `nil` but is no
        // list (its tail another type), which only `nil` fits; where a union
        // is, the union's pair if it has one, else its `nil`.
        if self.list_of_any(t) {
            let e = self.arena.resolve(expected);
            match self.arena.get(e).clone() {
                Ty::Nil => return Ok(e),
                Ty::Pair(_, tail, _, true) if self.arena.resolve(tail) != e => return Ok(self.arena.ty(Ty::Nil)),
                Ty::Union(ns) => {
                    let is = |c: &Self, n: TyId, nil: bool| match c.arena.get(c.arena.resolve(n)) {
                        Ty::Pair(..) => !nil,
                        Ty::Nil => nil,
                        _ => false,
                    };
                    if let Some(p) = ns.iter().find(|n| is(self, **n, false)) {
                        return self.instantiate_against(t, *p, span);
                    }
                    if let Some(n) = ns.iter().find(|n| is(self, **n, true)) {
                        return Ok(*n);
                    }
                }
                _ => {}
            }
        }
        let (kinds, inner) = self.binders_of(t);
        let mut u = Unknowns { kinds, solved: HashMap::new() };
        self.unify(inner, expected, &mut u, &mut HashSet::new());
        self.default_regions(&mut u);
        let map = self.finish(&u, span, t)?;
        self.check_bounds(&u.kinds, &map, span)?;
        self.check_finite_sizes(&u.kinds, &map, inner, span)?;
        let inst = self.subst(inner, &map);
        self.no_knot(inst, span)?;
        Ok(inst)
    }

    /// Whether `t` is a list, or a pair that may be `nil`, whose elements are
    /// a binder of its own: a type only the empty list has.
    pub(crate) fn list_of_any(&self, t: TyId) -> bool {
        let (kinds, inner) = self.binders_of(t);
        match self.arena.get(self.arena.resolve(inner)) {
            Ty::Pair(a, _, _, true) => {
                matches!(self.arena.get(self.arena.resolve(*a)), Ty::Var(v) if kinds.iter().any(|(k, _)| k == v))
            }
            _ => false,
        }
    }

    /// A result `(pairof A v R)`, `v` solved to `nil` and nothing expected
    /// of it, has `v` a `(listof A R)` instead (`DONE.md` §48): the pair is
    /// new, so no alias sees its tail as `nil` alone, and `(cons 1 nil)` is
    /// a list. Each argument is checked against what its parameter then is.
    fn widen_nil_tail(&mut self, result: TyId, u: &mut Unknowns) {
        let Ty::Pair(head, tail, region, _) = self.arena.get(self.arena.resolve(result)).clone() else { return };
        let Ty::Var(v) = *self.arena.get(self.arena.resolve(tail)) else { return };
        let Some(D::Type(t)) = u.solved.get(&v) else { return };
        if !u.is_unknown(v) || !matches!(self.arena.get(self.arena.resolve(*t)), Ty::Nil) {
            return;
        }
        let head = self.subst(head, &u.solved);
        if self.mentions_unknown_type(head, u) {
            return;
        }
        let slot = self.arena.ty(Ty::Link(None));
        let pair = self.arena.ty(Ty::Pair(head, slot, region, true));
        self.arena.set_link(slot, pair);
        let list = self.subst(slot, &u.solved);
        u.solved.insert(v, D::Type(list));
    }

    /// Branches' types, each `nil` (`nil_if_any`) the type `nil`, and, if
    /// one is, each pair one that may be `nil`: their join, if they have one,
    /// is then one of them.
    pub(crate) fn join_with_nil(&mut self, ts: &[TyId]) -> Vec<TyId> {
        let ts: Vec<TyId> = ts.iter().map(|t| self.nil_if_any(*t)).collect();
        if !ts.iter().any(|t| matches!(self.arena.get(self.arena.resolve(*t)), Ty::Nil)) {
            return ts;
        }
        ts.into_iter()
            .map(|t| match self.arena.get(self.arena.resolve(t)).clone() {
                Ty::Pair(a, b, r, false) => self.arena.ty(Ty::Pair(a, b, r, true)),
                _ => t,
            })
            .collect()
    }

    /// `car` or `cdr` of a union with a pair member (a `datum`, say) takes
    /// that member apart: every machine's `car` checks its argument is a
    /// pair, and traps if not, as it does on `nil` (TODO §51).
    fn partial_pair_argument(&mut self, e: ExpId, params: &[TyId], done: &mut [Synthesised], u: &mut Unknowns) {
        let car = |c: &Self| matches!(c.facts.standard_operator.get(&e), Some(s) if matches!(c.interner.name(*s), "car" | "cdr"));
        if !car(self) {
            return;
        }
        let Some(Some((t, eff))) = done.first().cloned() else { return };
        let Ty::Union(ms) = self.arena.get(self.arena.resolve(t)).clone() else { return };
        if let Some(&m) = ms.iter().find(|m| matches!(self.arena.get(self.arena.resolve(**m)), Ty::Pair(..))) {
            self.unify(params[0], m, u, &mut HashSet::new());
            done[0] = Some((m, eff));
        }
    }

    /// `t`, or, if a list of any elements (`nil`), the type `nil`.
    pub(crate) fn nil_if_any(&mut self, t: TyId) -> TyId {
        if self.list_of_any(t) { self.arena.ty(Ty::Nil) } else { t }
    }

    /// Give each region binder nothing has solved a fresh region of its own;
    /// or, if it has a bound, its bound, as solved (so `(rcons p x y)`,
    /// with nothing else saying, allocates at `p`'s own region).
    fn default_regions(&mut self, u: &mut Unknowns) {
        for (v, k) in u.kinds.clone() {
            if k == Kind::Region
                && !u.solved.contains_key(&v)
                && let Some(b) = self.arena.bound(v)
            {
                let b = match b {
                    Region::Var(w) => match u.solved.get(&w) {
                        Some(D::Region(x)) => *x,
                        _ if u.is_unknown(w) => continue,
                        _ => b,
                    },
                    b => b,
                };
                u.solved.insert(v, D::Region(b));
            }
        }
        for (v, k) in u.kinds.clone() {
            // A bounded binder waits for its bound to be solved.
            let waits = matches!(self.arena.bound(v), Some(Region::Var(w)) if u.is_unknown(w));
            if k == Kind::Region && !u.solved.contains_key(&v) && !waits {
                let r = self.fresh_region(v);
                u.solved.insert(v, D::Region(r));
            }
        }
    }

    /// Each bounded region binder, as solved, won't outlive its bound, as
    /// solved; or an error saying which would.
    pub(crate) fn check_bounds(&self, kinds: &[(DVar, Kind)], map: &HashMap<DVar, D>, span: fixpt_read::Span) -> R<()> {
        let region = |r: Region| match r {
            Region::Var(w) => match map.get(&w) {
                Some(D::Region(x)) => *x,
                _ => r,
            },
            r => r,
        };
        for (v, k) in kinds {
            // A `data` binder takes only data, at its place: the heap, or
            // the place its bound says (F13).
            if *k == Kind::Data {
                let Some(D::Type(t)) = map.get(v) else { continue };
                let name = self.interner.name(self.arena.dvar_name(*v));
                if !self.is_data(*t) {
                    return Err(FxError::at(span, format!("`{name}` is bound as data, and a {} is not data", self.show_ty(*t))));
                }
                let place = region(self.arena.bound(*v).unwrap_or(Region::Heap));
                if !self.is_data_at(*t, place) {
                    return Err(FxError::at(
                        span,
                        format!(
                            "`{name}` is bound as data at {}, and a {} is data in another place",
                            self.show_region(place),
                            self.show_ty(*t)
                        ),
                    ));
                }
                continue;
            }
            let Some(b) = self.arena.bound(*v) else { continue };
            let (r, b) = (region(Region::Var(*v)), region(b));
            if !self.arena.outlived(r, b) {
                return Err(FxError::at(
                    span,
                    format!(
                        "`{}` must not outlive `{}`, and {} could outlive {}",
                        self.interner.name(self.arena.dvar_name(*v)),
                        self.show_region(self.arena.bound(*v).expect("bounded")),
                        self.show_region(r),
                        self.show_region(b)
                    ),
                ));
            }
        }
        Ok(())
    }

    /// A region no value so far is in, named after the binder it stands for.
    /// Uninterned, so the program cannot name it by accident.
    fn fresh_region(&mut self, v: DVar) -> Region {
        let base = format!("@{}", self.interner.name(self.arena.dvar_name(v)));
        self.fresh_region_named(&base)
    }

    /// A region no value so far is in, and no program can name: `base`
    /// with a number, uninterned.
    pub(crate) fn fresh_region_named(&mut self, base: &str) -> Region {
        self.fresh_regions += 1;
        let name = format!("{base}.{}", self.fresh_regions);
        Region::Const(self.interner.uninterned(&name))
    }

    fn partial_map(&self, u: &Unknowns) -> HashMap<DVar, D> {
        u.solved.clone()
    }

    /// The whole solution: every type binder solved, effects defaulting to
    /// `pure`.
    fn finish(&self, u: &Unknowns, span: fixpt_read::Span, ft: TyId) -> R<HashMap<DVar, D>> {
        let mut map = u.solved.clone();
        // A `data` binder's place nothing else says is where its data is:
        // the one place its parts are in, or the heap (F13).
        for (v, k) in &u.kinds {
            if *k == Kind::Data
                && let Some(Region::Var(p)) = self.arena.bound(*v)
                && !map.contains_key(&p)
                && u.kinds.iter().any(|(w, _)| *w == p)
                && let Some(D::Type(t)) = map.get(v)
            {
                let mut places = Vec::new();
                self.data_places(*t, &mut std::collections::HashSet::new(), &mut places);
                match places[..] {
                    [] => {
                        map.insert(p, D::Region(Region::Heap));
                    }
                    [q] => {
                        map.insert(p, D::Region(q));
                    }
                    _ => {}
                }
            }
        }
        for (v, k) in &u.kinds {
            if map.contains_key(v) {
                continue;
            }
            match k {
                Kind::Effect => {
                    map.insert(*v, D::Effect(Effect::pure()));
                }
                // A convention nothing says is the program's.
                Kind::Conv => {
                    map.insert(*v, D::Conv(self.conv_default));
                }
                // A size nothing says is some size.
                Kind::Size => {
                    map.insert(*v, D::Size(Size::Finite));
                }
                Kind::Type | Kind::Data | Kind::Place | Kind::Arrow(_) => {
                    return Err(FxError::at(
                        span,
                        format!(
                            "`{}` cannot be inferred for {}: nothing here says what it is. Use `proj`, or `the`",
                            self.interner.name(self.arena.dvar_name(*v)),
                            self.show_ty(ft)
                        ),
                    ));
                }
                Kind::Region => unreachable!("defaulted"),
            }
        }
        Ok(map)
    }

    /// Whether no instantiation of `pattern` could fit `actual`: they are
    /// different constructors.
    /// An argument of the wrong shape altogether, among those found: the
    /// error, naming it.
    fn shape_errors(&mut self, args: &[ExpId], params: &[TyId], done: &[Synthesised], u: &Unknowns) -> R<()> {
        for (i, a) in args.iter().enumerate() {
            if let Some((t, _)) = done[i]
                && self.wrong_shape(params[i], t)
            {
                let map = self.partial_map(u);
                let p = self.subst(params[i], &map);
                let p = self.show_open(p, u);
                return Err(FxError::at(
                    self.arena.span_of(*a),
                    format!("argument {} is a {}, where a {} is expected", i + 1, self.show_ty(t), p),
                ));
            }
        }
        Ok(())
    }

    /// Whether no instantiation of a callee's `result` could fit `want`,
    /// what the context expects, by their outermost shapes. An unknown
    /// fits anything; a pair may be told to be a `nlist`.
    fn result_misfits(&self, want: TyId, result: TyId) -> bool {
        let (w, r) = (self.arena.resolve(want), self.arena.resolve(result));
        match (self.arena.get(w), self.arena.get(r)) {
            (_, Ty::Var(_)) | (Ty::NList { .. }, Ty::Pair(..)) => false,
            _ => self.wrong_shape(w, r),
        }
    }

    /// `t` as a message shows it, each type binder not yet solved shown as
    /// `?`: what it is is not known, and its name is the callee's own.
    fn show_open(&mut self, t: TyId, u: &Unknowns) -> String {
        let hole = self.interner.intern("?");
        let hole = self.arena.ty(Ty::Base(hole));
        let open: HashMap<DVar, D> =
            u.kinds.iter().filter(|(v, k)| matches!(k, Kind::Type) && !u.solved.contains_key(v)).map(|(v, _)| (*v, D::Type(hole))).collect();
        let t = self.subst(t, &open);
        self.show_ty(t)
    }

    fn wrong_shape(&self, pattern: TyId, actual: TyId) -> bool {
        let (p, a) = (self.arena.get(pattern).clone(), self.arena.get(actual).clone());
        match (&p, &a) {
            // An application may become anything its function gives.
            (Ty::Var(_) | Ty::App { .. }, _) | (_, Ty::Void) => false,
            // A union: only if what is given is of none of its shapes.
            (Ty::Union(_), _) => match (self.shape(pattern), self.shape(actual)) {
                (Some(w), Some(g)) => w & g == 0,
                _ => false,
            },
            (Ty::Subr { .. }, _) => a.as_subr().is_none(),
            // A `nlist` is a list.
            (Ty::Pair(..), Ty::NList { .. }) => false,
            // A `nat` is an `int`; a test's result, a `bool`.
            (Ty::Base(_), Ty::Nat(_) | Ty::Proving { .. }) => false,
            _ => std::mem::discriminant(&p) != std::mem::discriminant(&a),
        }
    }

    /// Whether `t` mentions a binder of any kind not yet solved.
    fn mentions_any_unknown(&self, t: TyId, u: &Unknowns) -> bool {
        let open = |v: DVar| u.is_unknown(v) && !u.solved.contains_key(&v);
        let region = |r: Region| matches!(r, Region::Var(v) | Region::Frozen(Some(v), _) if open(v));
        let effect = |e: &Effect| {
            e.0.iter().any(|a| match *a {
                Atom::Var(v) => open(v),
                Atom::App(n) => self.arena.effect_apps.mentions(n, &open),
                a => a.region().is_some_and(region),
            })
        };
        // A description: whether it is open, its types onto `stack`.
        let d_hit = |d: &D, stack: &mut Vec<TyId>| match d {
            D::Type(x) | D::Fun(x) => {
                stack.push(*x);
                false
            }
            D::Region(r) => region(*r),
            D::Effect(e) => effect(e),
            D::Size(z) => matches!(z, Size::Lin { terms, .. } if terms.iter().any(|(v, _)| open(*v))),
            D::Conv(c) => matches!(c, crate::ast::Conv::Var(v) if open(*v)),
        };
        let mut seen = HashSet::new();
        let mut stack = vec![t];
        while let Some(t) = stack.pop() {
            let t = self.arena.resolve(t);
            if !seen.insert(t) {
                continue;
            }
            let hit = match self.arena.get(t).clone() {
                Ty::Var(v) => open(v),
                Ty::Subr { conv, effect: e, params, result } => {
                    stack.extend(params);
                    stack.push(result);
                    effect(&e) || matches!(conv, Conv::Var(v) if open(v))
                }
                Ty::Poly { body, .. } => {
                    stack.push(body);
                    false
                }
                Ty::Ref(x, r) | Ty::MarkKey(x, r) | Ty::Array(x, r) | Ty::ICell(x, r) => {
                    stack.push(x);
                    region(r)
                }
                Ty::Place(r) => region(r),
                Ty::Pair(x, y, r, _) => {
                    stack.extend([x, y]);
                    region(r)
                }
                Ty::Bloblet { fields, region: r, .. } => {
                    stack.extend(fields);
                    region(r)
                }
                Ty::Product(parts) | Ty::Sum(parts) => {
                    stack.extend(parts.iter().map(|(_, t)| *t));
                    false
                }
                Ty::Union(ms) => {
                    stack.extend(ms);
                    false
                }
                Ty::Module { descs, vals, .. } => {
                    stack.extend(descs.iter().chain(&vals).map(|(_, t)| *t));
                    false
                }
                Ty::Select(..) | Ty::ParamSel(..) => false,
                Ty::PromptTag { answer: x, payload: y, effect: e, region: r }
                | Ty::Composable { arg: x, answer: y, effect: e, region: r } => {
                    stack.extend([x, y]);
                    region(r) || effect(&e)
                }
                Ty::Base(_) | Ty::Void | Ty::Nil | Ty::False | Ty::Proving { .. } | Ty::Link(_) => false,
                Ty::Nat(size) => matches!(&size, Size::Lin { terms, .. } if terms.iter().any(|(v, _)| open(*v))),
                Ty::NList { elem, size, region: r } => {
                    stack.push(elem);
                    region(r) || matches!(&size, Size::Lin { terms, .. } if terms.iter().any(|(v, _)| open(*v)))
                }
                Ty::Named { args, .. } => args.iter().fold(false, |hit, d| d_hit(d, &mut stack) || hit),
                Ty::App { fun, args } => {
                    stack.push(fun);
                    args.iter().fold(false, |hit, d| d_hit(d, &mut stack) || hit)
                }
                Ty::Lam { body, .. } => d_hit(&body, &mut stack),
            };
            if hit {
                return true;
            }
        }
        false
    }

    fn mentions_unknown_type(&self, t: TyId, u: &Unknowns) -> bool {
        let mut seen = HashSet::new();
        self.walk_vars(t, &mut seen, &mut |v| u.is_unknown(v) && !u.solved.contains_key(&v))
    }

    fn walk_vars(&self, t: TyId, seen: &mut HashSet<TyId>, hit: &mut dyn FnMut(DVar) -> bool) -> bool {
        let t = self.arena.resolve(t);
        if !seen.insert(t) {
            return false;
        }
        match self.arena.get(t).clone() {
            Ty::Var(v) => hit(v),
            Ty::Subr { params, result, .. } => {
                params.iter().any(|p| self.walk_vars(*p, seen, hit)) || self.walk_vars(result, seen, hit)
            }
            Ty::Poly { body, .. } => self.walk_vars(body, seen, hit),
            Ty::Ref(a, _) | Ty::MarkKey(a, _) | Ty::Array(a, _) | Ty::ICell(a, _) => self.walk_vars(a, seen, hit),
            Ty::Bloblet { fields, .. } => fields.iter().any(|f| self.walk_vars(*f, seen, hit)),
            Ty::Product(parts) | Ty::Sum(parts) => parts.iter().any(|(_, t)| self.walk_vars(*t, seen, hit)),
            Ty::Union(ms) => ms.iter().any(|t| self.walk_vars(*t, seen, hit)),
            Ty::Pair(a, b, _, _)
            | Ty::PromptTag { answer: a, payload: b, .. }
            | Ty::Composable { arg: a, answer: b, .. } => self.walk_vars(a, seen, hit) || self.walk_vars(b, seen, hit),
            Ty::Base(_) | Ty::Nat(_) | Ty::Void | Ty::Nil | Ty::False | Ty::Proving { .. } | Ty::Link(_) | Ty::Place(_) | Ty::Select(..) | Ty::ParamSel(..) => false,
            Ty::Module { descs, vals, .. } => descs.iter().chain(&vals).any(|(_, t)| self.walk_vars(*t, seen, hit)),
            Ty::Named { args, .. } => args.iter().any(|d| matches!(d, D::Type(x) | D::Fun(x) if self.walk_vars(*x, seen, hit))),
            Ty::App { fun, args } => {
                self.walk_vars(fun, seen, hit) || args.iter().any(|d| matches!(d, D::Type(x) | D::Fun(x) if self.walk_vars(*x, seen, hit)))
            }
            Ty::Lam { body, .. } => matches!(body, D::Type(x) | D::Fun(x) if self.walk_vars(x, seen, hit)),
            Ty::NList { elem, .. } => self.walk_vars(elem, seen, hit),
        }
    }

    // ------------------------------------------------------------- matching

    /// Solve binders in `pattern` so that `actual` fits it. Never fails:
    /// whatever cannot be matched is left for the subtype check that follows
    /// to report, in the program's terms.
    fn unify(&mut self, pattern: TyId, actual: TyId, u: &mut Unknowns, trail: &mut HashSet<(TyId, TyId)>) {
        let (p, a) = (self.arena.resolve(pattern), self.arena.resolve(actual));
        if !trail.insert((p, a)) {
            return;
        }
        let (pt, at) = (self.arena.get(p).clone(), self.arena.get(a).clone());
        if matches!(at, Ty::Void) && !matches!(pt, Ty::Var(v) if u.is_unknown(v) && !u.solved.contains_key(&v)) {
            // The bottom type fits anything, so it says nothing about what
            // fits — unless nothing else will: a binder only a `void` can
            // solve, such as the result of a loop that never returns.
            return;
        }
        match (pt, at) {
            (Ty::Var(v), _) if u.is_unknown(v) => match u.solved.get(&v) {
                None => {
                    u.solved.insert(v, D::Type(a));
                }
                Some(D::Type(prev)) => {
                    // The larger, where it stands for a whole argument; in
                    // a pair's contents, which are invariant, what it meets
                    // there (an argument's element over the expected
                    // type's: a non-`nil` pair where the context says one
                    // may be `nil`).
                    let prev = *prev;
                    let take = if self.unify_exact {
                        prev != a && (self.subtype(a, prev) || self.subtype(prev, a))
                    } else {
                        !self.subtype(a, prev) && self.subtype(prev, a)
                    };
                    if take {
                        u.solved.insert(v, D::Type(a));
                    }
                }
                Some(_) => {}
            },
            // A union expected: the member whose shapes hold the pattern's
            // (a `cons` where a list or an `int` is wanted, its pair).
            (ref q, Ty::Union(aa)) if !matches!(q, Ty::Union(_)) => {
                let Some(ps) = self.shape(p).filter(|s| *s != 0) else { return };
                if let Some(y) = aa.iter().find(|y| self.shape(**y).is_some_and(|s| s & ps == ps)) {
                    self.unify(p, *y, u, trail);
                }
            }
            (Ty::Subr { conv: pc, effect: pe, params: pp, result: pr }, at) => {
                let Some((ae, ap, ar)) = at.as_subr() else { return };
                if let Ty::Subr { conv: ac, .. } = at {
                    self.unify_conv(pc, ac, u);
                }
                if pp.len() != ap.len() {
                    return;
                }
                for (x, y) in pp.iter().zip(&ap) {
                    self.unify(*x, *y, u, trail);
                }
                self.unify(pr, ar, u, trail);
                self.unify_effect(&pe, &ae, u);
            }
            (Ty::Ref(x, r), Ty::Ref(y, s))
            | (Ty::MarkKey(x, r), Ty::MarkKey(y, s))
            | (Ty::Array(x, r), Ty::Array(y, s))
            | (Ty::ICell(x, r), Ty::ICell(y, s)) => {
                self.unify_region(r, s, u);
                self.unify(x, y, u, trail);
            }
            (Ty::Place(r), Ty::Place(s)) => self.unify_region(r, s, u),
            (Ty::Pair(x1, x2, r, _), Ty::Pair(y1, y2, s, _)) => {
                self.unify_region(r, s, u);
                let outer = std::mem::replace(&mut self.unify_exact, true);
                self.unify(x1, y1, u, trail);
                self.unify(x2, y2, u, trail);
                self.unify_exact = outer;
            }
            // Members by shape, which no two in a union share.
            (Ty::Union(pp), at) => {
                let actual: Vec<TyId> = match at {
                    Ty::Union(aa) => aa,
                    _ => vec![a],
                };
                for x in &pp {
                    if let Some(y) = actual.iter().find(|y| self.shape(**y).is_some() && self.shape(**y) == self.shape(*x)) {
                        self.unify(*x, *y, u, trail);
                    }
                }
            }
            (Ty::Product(pp), Ty::Product(pa)) | (Ty::Sum(pp), Ty::Sum(pa)) => {
                for (l, x) in &pp {
                    if let Some((_, y)) = pa.iter().find(|(m, _)| m == l) {
                        self.unify(*x, *y, u, trail);
                    }
                }
            }
            (Ty::Bloblet { fields: fp, region: r, .. }, Ty::Bloblet { fields: fa, region: s, .. }) if fp.len() == fa.len() => {
                self.unify_region(r, s, u);
                for (x, y) in fp.iter().zip(&fa) {
                    self.unify(*x, *y, u, trail);
                }
            }
            (
                Ty::PromptTag { answer: a1, payload: h1, effect: d1, region: r1 },
                Ty::PromptTag { answer: a2, payload: h2, effect: d2, region: r2 },
            )
            | (
                Ty::Composable { arg: h1, answer: a1, effect: d1, region: r1 },
                Ty::Composable { arg: h2, answer: a2, effect: d2, region: r2 },
            ) => {
                self.unify_region(r1, r2, u);
                self.unify(a1, a2, u, trail);
                self.unify(h1, h2, u, trail);
                self.unify_effect(&d1, &d2, u);
            }
            (Ty::NList { elem: x, size: m, region: r }, Ty::NList { elem: y, size: n, region: s }) => {
                self.unify_region(r, s, u);
                self.unify(x, y, u, trail);
                self.unify_size(&m, &n, u);
            }
            (Ty::Nat(m), Ty::Nat(n)) => self.unify_size(&m, &n, u),
            (Ty::Pair(x, t2, r, _), Ty::NList { elem: y, size, region: s }) => {
                self.unify_region(r, s, u);
                self.unify(x, y, u, trail);
                let tail = match size {
                    Size::Finite => a,
                    _ => self.arena.ty(Ty::NList { elem: y, size: self.tail_size(&size), region: s }),
                };
                self.unify(t2, tail, u, trail);
            }
            (Ty::Named { which: g, args: xs }, Ty::Named { which: h, args: ys }) if g == h => self.unify_ds(&xs, &ys, u, trail),
            // A function applied, against another applied to as many: the
            // function, if it is a binder still to be found, is the other's;
            // what each was given, matched. Nothing else is solved for: a
            // function binder applied, against any other type, waits for
            // `proj` or `the` (FX-91's choice, and Jones's).
            (Ty::App { fun: f, args: xs }, Ty::App { fun: g, args: ys }) if xs.len() == ys.len() => {
                if let Ty::Var(v) = self.arena.get(f).clone()
                    && u.is_unknown(v)
                    && !u.solved.contains_key(&v)
                {
                    u.solved.insert(v, D::Fun(g));
                }
                self.unify_ds(&xs, &ys, u, trail);
            }
            // The same against a generative type applied: the function is
            // the generative type's, given what it is given.
            (Ty::App { fun: f, args: xs }, Ty::Named { which, args: ys }) if xs.len() == ys.len() => {
                if let Ty::Var(v) = self.arena.get(f).clone()
                    && u.is_unknown(v)
                    && !u.solved.contains_key(&v)
                    && let Some(g) = self.generative_fun(which, self.arena.dvar_kind(v))
                {
                    u.solved.insert(v, D::Fun(g));
                }
                self.unify_ds(&xs, &ys, u, trail);
            }
            _ => {}
        }
    }

    /// Descriptions matched pairwise, as `unify` matches types.
    fn unify_ds(&mut self, xs: &[D], ys: &[D], u: &mut Unknowns, trail: &mut HashSet<(TyId, TyId)>) {
        for (x, y) in xs.iter().zip(ys) {
            match (x, y) {
                (D::Type(x), D::Type(y)) => self.unify(*x, *y, u, trail),
                (D::Region(r), D::Region(s)) => self.unify_region(*r, *s, u),
                (D::Effect(d), D::Effect(e)) => self.unify_effect(d, e, u),
                (D::Conv(c), D::Conv(d)) => self.unify_conv(*c, *d, u),
                (D::Fun(f), D::Fun(g)) => {
                    if let Ty::Var(v) = self.arena.get(*f).clone()
                        && u.is_unknown(v)
                        && !u.solved.contains_key(&v)
                    {
                        u.solved.insert(v, D::Fun(*g));
                    }
                }
                _ => {}
            }
        }
    }

    /// A convention binder takes the actual's convention, if nothing has yet.
    fn unify_conv(&self, pattern: Conv, actual: Conv, u: &mut Unknowns) {
        if let Conv::Var(v) = pattern
            && u.is_unknown(v)
            && !u.solved.contains_key(&v)
        {
            u.solved.insert(v, D::Conv(actual));
        }
    }

    /// Solve a size binder: a pattern `v + k` against a size `s` gives
    /// `v = s - k` (`finite` stays `finite`).
    fn unify_size(&self, p: &Size, a: &Size, u: &mut Unknowns) {
        let Size::Lin { k, terms } = p else { return };
        let [(v, 1)] = terms[..] else { return };
        if u.is_unknown(v) && !u.solved.contains_key(&v) {
            u.solved.insert(v, D::Size(a.plus(-*k)));
        }
    }

    fn unify_region(&self, p: Region, a: Region, u: &mut Unknowns) {
        if let Region::Var(v) = p
            && u.is_unknown(v)
            && !u.solved.contains_key(&v)
        {
            u.solved.insert(v, D::Region(a));
        }
        // A place frozen into, `(acyclic p)` or `(const p)`: the place is
        // the actual's (the heap's, where that is frozen into the heap).
        if let Region::Frozen(Some(v), _) = p
            && u.is_unknown(v)
            && !u.solved.contains_key(&v)
        {
            match a {
                Region::Frozen(Some(q), _) => {
                    u.solved.insert(v, D::Region(Region::Var(q)));
                }
                Region::Frozen(None, _) => {
                    u.solved.insert(v, D::Region(Region::Heap));
                }
                _ => {}
            }
        }
    }

    /// An effect binder in `pattern` takes all of `actual`: the least it can
    /// be for `actual` to fit, since effects combine by union. Regions named
    /// in the pattern's atoms are matched against the actual's atoms of the
    /// same kind when there is exactly one to match.
    fn unify_effect(&self, pattern: &Effect, actual: &Effect, u: &mut Unknowns) {
        for atom in &pattern.0 {
            match *atom {
                Atom::Var(v) if u.is_unknown(v) => {
                    let prev = match u.solved.get(&v) {
                        Some(D::Effect(e)) => e.clone(),
                        _ => Effect::pure(),
                    };
                    u.solved.insert(v, D::Effect(prev.union(actual)));
                }
                a => {
                    let Some(Region::Var(v)) = a.region() else { continue };
                    if !u.is_unknown(v) || u.solved.contains_key(&v) {
                        continue;
                    }
                    let same_kind: Vec<Region> = actual
                        .0
                        .iter()
                        .filter(|b| std::mem::discriminant(*b) == std::mem::discriminant(&a))
                        .filter_map(|b| b.region())
                        .collect();
                    if let [only] = same_kind[..] {
                        u.solved.insert(v, D::Region(only));
                    }
                }
            }
        }
    }
}
