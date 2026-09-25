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

use crate::ast::{Atom, D, DVar, Effect, Exp, ExpId, Kind, Region, Ty, TyId};
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
        let span = self.arena.span_of(e);
        let expected_ty = self.arena.get(expected).clone();
        match self.arena.exp_at(e).clone() {
            // Against a `poly` type, anything but a `plambda` is checked with
            // the binders held abstract, as though it were wrapped in a
            // `plambda` binding them — so it must be pure, as a `plambda`
            // body must.
            _ if matches!(expected_ty, Ty::Poly { .. }) && !matches!(self.arena.exp_at(e), Exp::PLambda { .. }) => {
                let Ty::Poly { body, .. } = expected_ty else { unreachable!() };
                let eff = self.check(e, body)?;
                if !eff.is_pure() {
                    return Err(FxError::at(span, format!("a polymorphic value must be pure, and this has {}", self.show_effect(&eff))));
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
            Exp::App { fun, args } => {
                let (t, eff) = self.synth_app(e, fun, &args, Some(expected))?;
                self.expect(e, t, expected)?;
                Ok(eff)
            }
            Exp::Var(s) if self.lookup(s).is_some_and(|t| matches!(self.arena.get(t), Ty::Poly { .. })) => {
                let t = self.lookup(s).expect("bound");
                let inst = self.instantiate_against(t, expected, span)?;
                self.expect(e, inst, expected)?;
                Ok(Effect::pure())
            }
            Exp::If { test, then, els } => {
                let te = self.check(test, self.bool_ty())?;
                let ae = self.check(then, expected)?;
                let be = self.check(els, expected)?;
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
            Exp::Let { bindings, body } => {
                let mut eff = Effect::pure();
                let mut bound = Vec::new();
                for (n, init) in &bindings {
                    let (t, ie) = self.synth(*init)?;
                    eff = eff.union(&ie);
                    bound.push((*n, t));
                }
                let depth = self.env.len();
                self.env.extend(bound);
                let r = self.check(body, expected);
                self.env.truncate(depth);
                Ok(self.mask(e, &eff.union(&r?), expected))
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
        Err(FxError::at(
            self.arena.span_of(e),
            format!("a {} is expected here, and this is a {}", self.show_ty(want), self.show_ty(got)),
        ))
    }

    // --------------------------------------------------------------- lambda

    /// A `lambda`'s type. `hint` supplies the types of parameters the
    /// program left out; without it, every parameter must have one.
    pub(crate) fn synth_lambda(&mut self, e: ExpId, hint: Option<&[TyId]>) -> R<(TyId, Effect)> {
        self.synth_lambda_as(e, hint, None)
    }

    /// The same, with the body checked against `result` when it is known.
    fn synth_lambda_as(&mut self, e: ExpId, hint: Option<&[TyId]>, result: Option<TyId>) -> R<(TyId, Effect)> {
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
        let depth = self.env.len();
        self.env.extend(typed.iter().copied());
        // The body's effect is masked *with the parameters in scope*: they
        // are free in the body, so what reaches them stays.
        let r = match result {
            Some(want) => self.check(body, want).map(|eff| (want, self.mask(body, &eff, want))),
            None => self.synth(body).map(|(t, eff)| (t, self.mask(body, &eff, t))),
        };
        self.env.truncate(depth);
        let (result, latent) = r?;
        let t = self.arena.ty(Ty::Subr { effect: latent, params: typed.iter().map(|(_, t)| *t).collect(), result });
        Ok((t, Effect::pure()))
    }

    fn unannotated_lambda(&self, e: ExpId) -> bool {
        matches!(self.arena.exp_at(e), Exp::Lambda { params, .. } if params.iter().any(|(_, t)| t.is_none()))
    }

    // ----------------------------------------------------------- application

    /// An application, with the operator instantiated first if it is
    /// polymorphic. `expected` is the type the application should have, when
    /// that is known; it helps solve the operator's binders.
    pub(crate) fn synth_app(&mut self, e: ExpId, fun: ExpId, args: &[ExpId], expected: Option<TyId>) -> R<(TyId, Effect)> {
        let span = self.arena.span_of(e);
        let (mut ft, fe) = self.synth(fun)?;
        let mut done: Vec<Synthesised> = vec![None; args.len()];
        if matches!(self.arena.get(ft), Ty::Poly { .. }) {
            let (inst, cached) = self.instantiate(ft, args, expected, span)?;
            ft = inst;
            done = cached;
        }
        let callee = self.arena.get(ft).clone();
        let Some((latent, params, result)) = callee.as_subr() else {
            return Err(FxError::at(span, format!("not a subroutine: {}", self.show_ty(ft))));
        };
        if params.len() != args.len() {
            return Err(FxError::at(span, format!("expected {} argument(s), got {}", params.len(), args.len())));
        }
        let mut effect = fe;
        for (i, (a, p)) in args.iter().zip(&params).enumerate() {
            let eff = match done[i].take() {
                Some((t, eff)) => {
                    if !self.subtype(t, *p) {
                        return Err(FxError::at(
                            self.arena.span_of(*a),
                            format!("argument {} is a {}, where a {} is expected", i + 1, self.show_ty(t), self.show_ty(*p)),
                        ));
                    }
                    eff
                }
                None => self.check(*a, *p).map_err(|err| self.as_argument(err, *a, i))?,
            };
            effect = effect.union(&eff);
        }
        let effect = effect.union(&latent);
        let effect = self.mask(e, &effect, result);
        Ok((result, effect))
    }

    /// An argument that failed to check is reported as that argument.
    fn as_argument(&self, err: FxError, a: ExpId, i: usize) -> FxError {
        if err.span == self.arena.span_of(a) && err.message.starts_with("a ") && err.message.contains(" is expected here") {
            let rest = err.message.trim_start_matches("a ");
            if let Some((want, got)) = rest.split_once(" is expected here, and this is a ") {
                return FxError::at(err.span, format!("argument {} is a {got}, where a {want} is expected", i + 1));
            }
        }
        err
    }

    // --------------------------------------------------------- instantiation

    /// The binders of `t`, through every nested `poly`, and the type under
    /// them all.
    fn binders_of(&self, t: TyId) -> (Vec<(DVar, Kind)>, TyId) {
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
        ft: TyId,
        args: &[ExpId],
        expected: Option<TyId>,
        span: fixpt_read::Span,
    ) -> R<(TyId, Vec<Synthesised>)> {
        let (kinds, inner) = self.binders_of(ft);
        let Some((_, params, result)) = self.arena.get(inner).as_subr() else {
            return Err(FxError::at(span, format!("not a subroutine, even once projected: {}", self.show_ty(ft))));
        };
        if params.len() != args.len() {
            return Err(FxError::at(span, format!("expected {} argument(s), got {}", params.len(), args.len())));
        }
        let mut u = Unknowns { kinds, solved: HashMap::new() };
        let mut done: Vec<Synthesised> = vec![None; args.len()];
        // What the arguments are, except the ones that need to be told.
        for (i, a) in args.iter().enumerate() {
            if self.unannotated_lambda(*a) {
                continue;
            }
            let (t, eff) = self.synth(*a)?;
            if matches!(self.arena.get(t), Ty::Poly { .. }) {
                continue;
            }
            self.unify(params[i], t, &mut u, &mut HashSet::new());
            done[i] = Some((t, eff));
        }
        // What the whole is expected to be.
        if let Some(want) = expected {
            self.unify(result, want, &mut u, &mut HashSet::new());
        }
        // The arguments that needed telling: each is checked against its
        // parameter as solved so far, and what it turns out to be solves more.
        for (i, a) in args.iter().enumerate() {
            if done[i].is_some() {
                continue;
            }
            self.default_regions(&mut u);
            let map = self.partial_map(&u);
            let p = self.subst(params[i], &map);
            if self.mentions_unknown_type(p, &u) {
                return Err(FxError::at(
                    self.arena.span_of(*a),
                    format!(
                        "argument {} must be a {}, which is not yet known here; give the other arguments first, or `proj` the operator",
                        i + 1,
                        self.show_ty(p)
                    ),
                ));
            }
            if self.unannotated_lambda(*a) {
                let hint = self.arena.get(p).as_subr().map(|(_, ps, _)| ps);
                let (t, eff) = self.synth_lambda(*a, hint.as_deref())?;
                self.unify(params[i], t, &mut u, &mut HashSet::new());
                done[i] = Some((t, eff));
            } else {
                let eff = self.check(*a, p)?;
                done[i] = Some((p, eff));
            }
        }
        // An argument of the wrong shape altogether is the error to report,
        // before any binder it left unsolved.
        for (i, a) in args.iter().enumerate() {
            if let Some((t, _)) = done[i]
                && self.wrong_shape(params[i], t)
            {
                let map = self.partial_map(&u);
                let p = self.subst(params[i], &map);
                return Err(FxError::at(
                    self.arena.span_of(*a),
                    format!("argument {} is a {}, where a {} is expected", i + 1, self.show_ty(t), self.show_ty(p)),
                ));
            }
        }
        self.default_regions(&mut u);
        let map = self.finish(&u, span, ft)?;
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
        let (kinds, inner) = self.binders_of(t);
        let mut u = Unknowns { kinds, solved: HashMap::new() };
        self.unify(inner, expected, &mut u, &mut HashSet::new());
        self.default_regions(&mut u);
        let map = self.finish(&u, span, t)?;
        Ok(self.subst(inner, &map))
    }

    /// Give each region binder nothing has solved a fresh region of its own.
    fn default_regions(&mut self, u: &mut Unknowns) {
        for (v, k) in u.kinds.clone() {
            if k == Kind::Region && !u.solved.contains_key(&v) {
                let r = self.fresh_region(v);
                u.solved.insert(v, D::Region(r));
            }
        }
    }

    /// A region no value so far is in, named after the binder it stands for.
    /// Uninterned, so the program cannot name it by accident.
    fn fresh_region(&mut self, v: DVar) -> Region {
        self.fresh_regions += 1;
        let name = format!("@{}.{}", self.interner.name(self.arena.dvar_name(v)), self.fresh_regions);
        Region::Const(self.interner.uninterned(&name))
    }

    fn partial_map(&self, u: &Unknowns) -> HashMap<DVar, D> {
        u.solved.clone()
    }

    /// The whole solution: every type binder solved, effects defaulting to
    /// `pure`.
    fn finish(&self, u: &Unknowns, span: fixpt_read::Span, ft: TyId) -> R<HashMap<DVar, D>> {
        let mut map = u.solved.clone();
        for (v, k) in &u.kinds {
            if map.contains_key(v) {
                continue;
            }
            match k {
                Kind::Effect => {
                    map.insert(*v, D::Effect(Effect::pure()));
                }
                Kind::Type => {
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
    fn wrong_shape(&self, pattern: TyId, actual: TyId) -> bool {
        let (p, a) = (self.arena.get(pattern).clone(), self.arena.get(actual).clone());
        match (&p, &a) {
            (Ty::Var(_), _) | (_, Ty::Void) => false,
            (Ty::Subr { .. }, _) => a.as_subr().is_none(),
            _ => std::mem::discriminant(&p) != std::mem::discriminant(&a),
        }
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
            Ty::Ref(a, _) | Ty::MarkKey(a, _) => self.walk_vars(a, seen, hit),
            Ty::Pair(a, b, _)
            | Ty::PromptTag { answer: a, payload: b, .. }
            | Ty::Composable { arg: a, answer: b, .. } => self.walk_vars(a, seen, hit) || self.walk_vars(b, seen, hit),
            Ty::Base(_) | Ty::Void | Ty::Link(_) => false,
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
        if matches!(at, Ty::Void) {
            // The bottom type says nothing about what fits.
            return;
        }
        match (pt, at) {
            (Ty::Var(v), _) if u.is_unknown(v) => match u.solved.get(&v) {
                None => {
                    u.solved.insert(v, D::Type(a));
                }
                Some(D::Type(prev)) => {
                    let prev = *prev;
                    if !self.subtype(a, prev) && self.subtype(prev, a) {
                        u.solved.insert(v, D::Type(a));
                    }
                }
                Some(_) => {}
            },
            (Ty::Subr { effect: pe, params: pp, result: pr }, at) => {
                let Some((ae, ap, ar)) = at.as_subr() else { return };
                if pp.len() != ap.len() {
                    return;
                }
                for (x, y) in pp.iter().zip(&ap) {
                    self.unify(*x, *y, u, trail);
                }
                self.unify(pr, ar, u, trail);
                self.unify_effect(&pe, &ae, u);
            }
            (Ty::Ref(x, r), Ty::Ref(y, s)) | (Ty::MarkKey(x, r), Ty::MarkKey(y, s)) => {
                self.unify_region(r, s, u);
                self.unify(x, y, u, trail);
            }
            (Ty::Pair(x1, x2, r), Ty::Pair(y1, y2, s)) => {
                self.unify_region(r, s, u);
                self.unify(x1, y1, u, trail);
                self.unify(x2, y2, u, trail);
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
            _ => {}
        }
    }

    fn unify_region(&self, p: Region, a: Region, u: &mut Unknowns) {
        if let Region::Var(v) = p
            && u.is_unknown(v)
            && !u.solved.contains_key(&v)
        {
            u.solved.insert(v, D::Region(a));
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
