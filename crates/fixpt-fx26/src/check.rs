//! Checking the kernel: a type and an effect for every expression.
//!
//! The rules are KFX's (PLDI '89, p. 3), n-ary as FX-87 writes them:
//!
//! * a variable, a literal, a `lambda` and a `plambda` are pure;
//! * an application's effect is the operator's, the arguments', and the
//!   operator's latent effect, combined;
//! * a `plambda`'s body must be pure;
//! * `proj` substitutes descriptions for a `poly`'s binders.
//!
//! **Masking** is applied at every expression that combines effects —
//! application, `lambda` (whose masked body effect becomes the latent
//! effect), `let`, `letrec`, `begin`, `if`, `proj` — as FX-87's reference does
//! (`erase-effect`, called from `desc-of-begin`, `-lambda`, `-letrec`, `-app`
//! in `type-check.lisp`). The rule for each region `r` of an effect:
//!
//! * if `r` appears in the type of a free variable, everything on `r` stays;
//! * otherwise everything on `r` goes — except that when `r` appears in the
//!   result type, `(alloc r)` stays (FX-87: the cell escapes), and so do
//!   `(goto r)` and `(comefrom r)` (PLDI '89, p. 6: a control effect is masked
//!   only if the expression neither imports variables nor returns values whose
//!   types mention `r` — stricter than FX-87's rule for reads and writes, and
//!   p. 7 shows why).
//!
//! **Prompts** delimit control on their tag's region, under a condition of
//! their own: see `synth_prompt`.

use crate::ast::{Arena, Atom, D, DVar, Effect, Exp, ExpId, Kind, Region, Ty, TyId};
use crate::error::{FxError, R};
use crate::parse::DScope;
use fixpt_read::{Interner, Reader, Sym, Syntax, SyntaxProfile};
use std::collections::{HashMap, HashSet};

pub struct Checker {
    pub arena: Arena,
    pub interner: Interner,
    /// Value variables in scope, innermost last.
    pub env: Vec<(Sym, TyId)>,
    /// Description names in scope while parsing, innermost last.
    pub(crate) dscope: Vec<(Sym, DScope)>,
    pub(crate) base: HashMap<Sym, TyId>,
    pub(crate) void: TyId,
    int: TyId,
    bool_: TyId,
    string: TyId,
    unit: TyId,
    /// Mask at every expression, as the rules say. Off only to observe an
    /// effect *before* masking, which is what some of the paper's claims are
    /// about.
    pub masking: bool,
}

/// What checking an expression found.
#[derive(Clone, Debug)]
pub struct Checked {
    pub ty: TyId,
    pub effect: Effect,
}

impl Default for Checker {
    fn default() -> Checker {
        Checker::new()
    }
}

impl Checker {
    /// A checker with the initial environment of `crate::standard`.
    pub fn new() -> Checker {
        let mut interner = Interner::new();
        let mut arena = Arena::default();
        let mut base = HashMap::new();
        let mut basic = |name: &str| {
            let sym = interner.intern(name);
            let t = arena.ty(Ty::Base(sym));
            base.insert(sym, t);
            t
        };
        let int = basic("int");
        let bool_ = basic("bool");
        let string = basic("string");
        let unit = basic("unit");
        basic("char");
        let void = arena.ty(Ty::Void);
        let mut c = Checker {
            arena,
            interner,
            env: Vec::new(),
            dscope: Vec::new(),
            base,
            void,
            int,
            bool_,
            string,
            unit,
            masking: true,
        };
        for (name, ty) in crate::standard::ENTRIES {
            c.bind(name, ty).unwrap_or_else(|e| panic!("the standard type of `{name}` is wrong: {e}"));
        }
        c
    }

    fn read(&mut self, text: &str) -> R<Vec<Syntax>> {
        let mut interner = std::mem::take(&mut self.interner);
        let r = Reader::new(text, fixpt_read::FileId(0), SyntaxProfile::FX87, &mut interner).read_all();
        self.interner = interner;
        r.map_err(|e| FxError::at(e.span, e.message))
    }

    /// Bind `name` to a value of the type written `ty` — how the initial
    /// environment is built, and how a test supplies an example's free
    /// variables.
    pub fn bind(&mut self, name: &str, ty: &str) -> R<()> {
        let forms = self.read(ty)?;
        let [form] = &forms[..] else {
            return Err(FxError::at(fixpt_read::Span::new(fixpt_read::FileId(0), 0, 0), "one type"));
        };
        let t = self.parse_type(form)?;
        let sym = self.interner.intern(name);
        self.env.push((sym, t));
        Ok(())
    }

    /// Check the one expression written `text`.
    pub fn check_str(&mut self, text: &str) -> R<Checked> {
        let forms = self.read(text)?;
        let [form] = &forms[..] else {
            return Err(FxError::at(fixpt_read::Span::new(fixpt_read::FileId(0), 0, 0), "one expression"));
        };
        let e = self.parse_exp(form)?;
        let (ty, effect) = self.synth(e)?;
        Ok(Checked { ty, effect })
    }

    /// A type written as text, for comparing against.
    pub fn type_of_str(&mut self, text: &str) -> R<TyId> {
        let forms = self.read(text)?;
        let [form] = &forms[..] else {
            return Err(FxError::at(fixpt_read::Span::new(fixpt_read::FileId(0), 0, 0), "one type"));
        };
        self.parse_type(form)
    }

    /// An effect written as text.
    pub fn effect_of_str(&mut self, text: &str) -> R<Effect> {
        let forms = self.read(text)?;
        self.parse_effect(&forms[0])
    }

    /// The region written as text.
    pub fn region_of_str(&mut self, text: &str) -> R<Region> {
        let forms = self.read(text)?;
        self.parse_region(&forms[0])
    }

    fn lookup(&self, s: Sym) -> Option<TyId> {
        self.env.iter().rev().find(|(n, _)| *n == s).map(|(_, t)| *t)
    }

    // ------------------------------------------------------------ synthesis
    pub fn synth(&mut self, e: ExpId) -> R<(TyId, Effect)> {
        let span = self.arena.span_of(e);
        match self.arena.exp_at(e).clone() {
            Exp::Var(s) => match self.lookup(s) {
                Some(t) => Ok((t, Effect::pure())),
                None => Err(FxError::at(span, format!("unbound variable `{}`", self.interner.name(s)))),
            },
            Exp::Int(_) => Ok((self.int, Effect::pure())),
            Exp::Bool(_) => Ok((self.bool_, Effect::pure())),
            Exp::Str(_) => Ok((self.string, Effect::pure())),
            Exp::Unit => Ok((self.unit, Effect::pure())),
            Exp::Lambda { params, body } => {
                let depth = self.env.len();
                self.env.extend(params.iter().copied());
                // The body's effect is masked *with the parameters in scope*:
                // they are free in the body, so what reaches them stays.
                let r = self.synth(body).map(|(t, eff)| (t, self.mask(body, &eff, t)));
                self.env.truncate(depth);
                let (result, latent) = r?;
                let t = self.arena.ty(Ty::Subr {
                    effect: latent,
                    params: params.iter().map(|(_, t)| *t).collect(),
                    result,
                });
                Ok((t, Effect::pure()))
            }
            Exp::App { fun, args } => {
                let (ft, fe) = self.synth(fun)?;
                let mut effect = fe;
                let mut arg_tys = Vec::new();
                for a in &args {
                    let (t, eff) = self.synth(*a)?;
                    effect = effect.union(&eff);
                    arg_tys.push(t);
                }
                let callee = self.arena.get(ft).clone();
                let Some((latent, params, result)) = callee.as_subr() else {
                    return Err(FxError::at(
                        span,
                        match callee {
                            Ty::Poly { .. } => "a polymorphic value must be instantiated with `proj` before it is applied".into(),
                            _ => format!("not a subroutine: {}", self.show_ty(ft)),
                        },
                    ));
                };
                if params.len() != args.len() {
                    return Err(FxError::at(span, format!("expected {} argument(s), got {}", params.len(), args.len())));
                }
                for (i, (a, p)) in arg_tys.iter().zip(&params).enumerate() {
                    if !self.subtype(*a, *p) {
                        return Err(FxError::at(
                            self.arena.span_of(args[i]),
                            format!("argument {} is a {}, where a {} is expected", i + 1, self.show_ty(*a), self.show_ty(*p)),
                        ));
                    }
                }
                let effect = effect.union(&latent);
                let effect = self.mask(e, &effect, result);
                Ok((result, effect))
            }
            Exp::PLambda { binders, body } => {
                let (t, eff) = self.synth(body)?;
                if !eff.is_pure() {
                    return Err(FxError::at(span, format!("a `plambda` body must be pure, and this one has {}", self.show_effect(&eff))));
                }
                Ok((self.arena.ty(Ty::Poly { binders, body: t }), Effect::pure()))
            }
            Exp::Proj { body, args } => {
                let (t, eff) = self.synth(body)?;
                let Ty::Poly { binders, body: inner } = self.arena.get(t).clone() else {
                    return Err(FxError::at(span, format!("`proj` needs a polymorphic value, not a {}", self.show_ty(t))));
                };
                if binders.len() != args.len() {
                    return Err(FxError::at(span, format!("this `poly` binds {} description(s); `proj` gave {}", binders.len(), args.len())));
                }
                let mut map = HashMap::new();
                for ((v, k), d) in binders.iter().zip(args) {
                    let ok = matches!((k, &d), (Kind::Region, D::Region(_)) | (Kind::Effect, D::Effect(_)) | (Kind::Type, D::Type(_)));
                    if !ok {
                        return Err(FxError::at(span, format!("`{}` is bound as a {k:?}, and the description given is not one", self.interner.name(self.arena.dvar_name(*v)))));
                    }
                    map.insert(*v, d);
                }
                let result = self.subst(inner, &map);
                let eff = self.mask(e, &eff, result);
                Ok((result, eff))
            }
            Exp::If { test, then, els } => {
                let (tt, te) = self.synth(test)?;
                if !self.subtype(tt, self.bool_) {
                    return Err(FxError::at(self.arena.span_of(test), "an `if` test must be a bool"));
                }
                let (a, ae) = self.synth(then)?;
                let (b, be) = self.synth(els)?;
                let t = if self.subtype(a, b) {
                    b
                } else if self.subtype(b, a) {
                    a
                } else {
                    return Err(FxError::at(span, format!("the branches are a {} and a {}", self.show_ty(a), self.show_ty(b))));
                };
                let eff = self.mask(e, &te.union(&ae).union(&be), t);
                Ok((t, eff))
            }
            Exp::Letrec { bindings, body } => {
                let depth = self.env.len();
                self.env.extend(bindings.iter().map(|(n, t, _)| (*n, *t)));
                let r = (|| {
                    let mut eff = Effect::pure();
                    for (n, t, init) in &bindings {
                        let (it, ie) = self.synth(*init)?;
                        if !self.subtype(it, *t) {
                            return Err(FxError::at(self.arena.span_of(*init), format!("`{}` is declared a {}, and its initialiser is a {}", self.interner.name(*n), self.show_ty(*t), self.show_ty(it))));
                        }
                        eff = eff.union(&ie);
                    }
                    let (bt, be) = self.synth(body)?;
                    Ok((bt, eff.union(&be)))
                })();
                self.env.truncate(depth);
                let (t, eff) = r?;
                let eff = self.mask(e, &eff, t);
                Ok((t, eff))
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
                let r = self.synth(body);
                self.env.truncate(depth);
                let (t, be) = r?;
                let eff = self.mask(e, &eff.union(&be), t);
                Ok((t, eff))
            }
            Exp::Prompt { tag, body, handler } => self.synth_prompt(e, tag, body, handler),
            Exp::Begin(items) => {
                let mut eff = Effect::pure();
                let mut last = self.unit;
                for i in &items {
                    let (t, ie) = self.synth(*i)?;
                    eff = eff.union(&ie);
                    last = t;
                }
                let eff = self.mask(e, &eff, last);
                Ok((last, eff))
            }
        }
    }

    // --------------------------------------------------------------- masking
    /// Remove from `effect` what cannot be observed outside expression `e`,
    /// whose type is `result`. See the module docs for the rule.
    pub(crate) fn mask(&self, e: ExpId, effect: &Effect, result: TyId) -> Effect {
        if !self.masking || effect.is_pure() {
            return effect.clone();
        }
        let mut visible = HashSet::new();
        for v in self.free_vars(e) {
            if let Some(t) = self.lookup(v) {
                self.regions_in(t, &mut visible);
            }
        }
        let mut in_result = HashSet::new();
        self.regions_in(result, &mut in_result);
        let kept = effect
            .0
            .iter()
            .copied()
            .filter(|a| match a.region() {
                None => true,
                Some(r) if visible.contains(&r) => true,
                Some(r) if in_result.contains(&r) => {
                    matches!(a, Atom::Alloc(_) | Atom::Goto(_) | Atom::Comefrom(_))
                }
                Some(_) => false,
            })
            .collect();
        Effect(kept)
    }

    /// The value variables free in `e`.
    fn free_vars(&self, e: ExpId) -> Vec<Sym> {
        let mut out = Vec::new();
        self.free_into(e, &mut Vec::new(), &mut out);
        out
    }

    fn free_into(&self, e: ExpId, bound: &mut Vec<Sym>, out: &mut Vec<Sym>) {
        match self.arena.exp_at(e).clone() {
            Exp::Var(s) => {
                if !bound.contains(&s) && !out.contains(&s) {
                    out.push(s);
                }
            }
            Exp::Int(_) | Exp::Bool(_) | Exp::Str(_) | Exp::Unit => {}
            Exp::Lambda { params, body } => {
                let depth = bound.len();
                bound.extend(params.iter().map(|(n, _)| *n));
                self.free_into(body, bound, out);
                bound.truncate(depth);
            }
            Exp::App { fun, args } => {
                self.free_into(fun, bound, out);
                for a in args {
                    self.free_into(a, bound, out);
                }
            }
            Exp::PLambda { body, .. } | Exp::Proj { body, .. } => self.free_into(body, bound, out),
            Exp::If { test, then, els } => {
                for x in [test, then, els] {
                    self.free_into(x, bound, out);
                }
            }
            Exp::Letrec { bindings, body } => {
                let depth = bound.len();
                bound.extend(bindings.iter().map(|(n, _, _)| *n));
                for (_, _, init) in &bindings {
                    self.free_into(*init, bound, out);
                }
                self.free_into(body, bound, out);
                bound.truncate(depth);
            }
            Exp::Let { bindings, body } => {
                for (_, init) in &bindings {
                    self.free_into(*init, bound, out);
                }
                let depth = bound.len();
                bound.extend(bindings.iter().map(|(n, _)| *n));
                self.free_into(body, bound, out);
                bound.truncate(depth);
            }
            Exp::Begin(items) => {
                for i in items {
                    self.free_into(i, bound, out);
                }
            }
            Exp::Prompt { tag, body, handler } => {
                for x in [tag, body, handler] {
                    self.free_into(x, bound, out);
                }
            }
        }
    }

    /// Every region mentioned in type `t`, following recursive types once.
    pub fn regions_in(&self, t: TyId, out: &mut HashSet<Region>) {
        let mut seen = HashSet::new();
        self.regions_walk(t, &mut seen, out);
    }

    fn regions_walk(&self, t: TyId, seen: &mut HashSet<TyId>, out: &mut HashSet<Region>) {
        let t = self.arena.resolve(t);
        if !seen.insert(t) {
            return;
        }
        match self.arena.get(t).clone() {
            Ty::Base(_) | Ty::Void | Ty::Var(_) | Ty::Link(None) => {}
            Ty::Link(Some(_)) => unreachable!("resolved"),
            Ty::Subr { effect, params, result } => {
                out.extend(effect.0.iter().filter_map(|a| a.region()));
                for p in params {
                    self.regions_walk(p, seen, out);
                }
                self.regions_walk(result, seen, out);
            }
            Ty::Poly { body, .. } => self.regions_walk(body, seen, out),
            Ty::Ref(a, r) => {
                out.insert(r);
                self.regions_walk(a, seen, out);
            }
            Ty::Pair(a, b, r) => {
                out.insert(r);
                self.regions_walk(a, seen, out);
                self.regions_walk(b, seen, out);
            }
            Ty::PromptTag { answer: a, payload: b, effect, region: r }
            | Ty::Composable { arg: b, answer: a, effect, region: r } => {
                out.insert(r);
                out.extend(effect.0.iter().filter_map(|x| x.region()));
                self.regions_walk(a, seen, out);
                self.regions_walk(b, seen, out);
            }
            Ty::MarkKey(t, r) => {
                out.insert(r);
                self.regions_walk(t, seen, out);
            }
        }
    }

    // ------------------------------------------------------------- subtyping
    /// `a ≤ b`. Recursive types are compared coinductively: a pair already
    /// being compared is assumed to hold, which is what makes comparing two
    /// cycles terminate — FX-87's `trail`.
    pub fn subtype(&mut self, a: TyId, b: TyId) -> bool {
        self.sub(a, b, &mut HashSet::new())
    }

    fn sub(&mut self, a: TyId, b: TyId, trail: &mut HashSet<(TyId, TyId)>) -> bool {
        let (a, b) = (self.arena.resolve(a), self.arena.resolve(b));
        if a == b || !trail.insert((a, b)) {
            return true;
        }
        let (ta, tb) = (self.arena.get(a).clone(), self.arena.get(b).clone());
        // A composable continuation can be called, so it can stand where a
        // subroutine is wanted.
        if let (Ty::Composable { .. }, Ty::Subr { .. }) = (&ta, &tb) {
            let (ea, pa, ra) = ta.as_subr().expect("callable");
            let (eb, pb, rb) = tb.as_subr().expect("callable");
            return pa.len() == pb.len()
                && ea.within(&eb)
                && pa.iter().zip(&pb).all(|(x, y)| self.sub(*y, *x, trail))
                && self.sub(ra, rb, trail);
        }
        match (ta, tb) {
            // `void` is the bottom type: nothing is ever returned as one.
            (Ty::Void, _) => true,
            (Ty::Base(x), Ty::Base(y)) => x == y,
            (Ty::Var(x), Ty::Var(y)) => x == y,
            (
                Ty::Subr { effect: ea, params: pa, result: ra },
                Ty::Subr { effect: eb, params: pb, result: rb },
            ) => {
                pa.len() == pb.len()
                    && ea.within(&eb)
                    && pa.iter().zip(&pb).all(|(x, y)| self.sub(*y, *x, trail))
                    && self.sub(ra, rb, trail)
            }
            // References and pairs are mutable, so their contents are
            // invariant: FX-87's `ref` rule, and its pairs.
            (Ty::Ref(x, r), Ty::Ref(y, s)) => r == s && self.sub(x, y, trail) && self.sub(y, x, trail),
            (Ty::Pair(x1, x2, r), Ty::Pair(y1, y2, s)) => {
                r == s
                    && self.sub(x1, y1, trail)
                    && self.sub(y1, x1, trail)
                    && self.sub(x2, y2, trail)
                    && self.sub(y2, x2, trail)
            }
            // A tag both delivers and receives values of its types, so it is
            // invariant in all of them, as a reference is in its contents.
            (
                Ty::PromptTag { answer: a1, payload: h1, effect: d1, region: r1 },
                Ty::PromptTag { answer: a2, payload: h2, effect: d2, region: r2 },
            ) => {
                r1 == r2
                    && d1 == d2
                    && self.sub(a1, a2, trail)
                    && self.sub(a2, a1, trail)
                    && self.sub(h1, h2, trail)
                    && self.sub(h2, h1, trail)
            }
            // Called like a subroutine: contravariant in what it takes,
            // covariant in what it gives and does.
            (
                Ty::Composable { arg: t1, answer: a1, effect: d1, region: r1 },
                Ty::Composable { arg: t2, answer: a2, effect: d2, region: r2 },
            ) => r1 == r2 && d1.within(&d2) && self.sub(t2, t1, trail) && self.sub(a1, a2, trail),
            (Ty::MarkKey(x, r), Ty::MarkKey(y, s)) => r == s && self.sub(x, y, trail) && self.sub(y, x, trail),
            (Ty::Poly { binders: ba, body: xa }, Ty::Poly { binders: bb, body: xb }) => {
                if ba.len() != bb.len() || ba.iter().zip(&bb).any(|((_, k1), (_, k2))| k1 != k2) {
                    return false;
                }
                // Compare the bodies with `b`'s binders renamed to `a`'s.
                let map: HashMap<DVar, D> = bb
                    .iter()
                    .zip(&ba)
                    .map(|((vb, k), (va, _))| {
                        let d = match k {
                            Kind::Region => D::Region(Region::Var(*va)),
                            Kind::Effect => D::Effect(Effect::atom(Atom::Var(*va))),
                            Kind::Type => D::Type(self.arena.ty(Ty::Var(*va))),
                        };
                        (*vb, d)
                    })
                    .collect();
                let xb = self.subst(xb, &map);
                self.sub(xa, xb, trail)
            }
            _ => false,
        }
    }

    // ---------------------------------------------------------- substitution
    /// `t` with each binder in `map` replaced — what `proj` does. Recursive
    /// types are copied as cycles: each node is given its slot before its
    /// children are built.
    pub fn subst(&mut self, t: TyId, map: &HashMap<DVar, D>) -> TyId {
        self.subst_memo(t, map, &mut HashMap::new())
    }

    fn subst_memo(&mut self, t: TyId, map: &HashMap<DVar, D>, memo: &mut HashMap<TyId, TyId>) -> TyId {
        let t = self.arena.resolve(t);
        if let Some(&n) = memo.get(&t) {
            return n;
        }
        let ty = self.arena.get(t).clone();
        match ty {
            Ty::Base(_) | Ty::Void | Ty::Link(None) => return t,
            Ty::Var(v) => {
                return match map.get(&v) {
                    Some(D::Type(x)) => *x,
                    _ => t,
                };
            }
            _ => {}
        }
        let slot = self.arena.ty(Ty::Link(None));
        memo.insert(t, slot);
        let region = |r: Region| match r {
            Region::Var(v) => match map.get(&v) {
                Some(D::Region(x)) => *x,
                _ => r,
            },
            c => c,
        };
        let new = match ty {
            Ty::Subr { effect, params, result } => {
                let effect = subst_effect(&effect, map);
                let params = params.iter().map(|p| self.subst_memo(*p, map, memo)).collect();
                let result = self.subst_memo(result, map, memo);
                Ty::Subr { effect, params, result }
            }
            Ty::Poly { binders, body } => Ty::Poly { binders, body: self.subst_memo(body, map, memo) },
            Ty::Ref(a, r) => Ty::Ref(self.subst_memo(a, map, memo), region(r)),
            Ty::Pair(a, b, r) => Ty::Pair(self.subst_memo(a, map, memo), self.subst_memo(b, map, memo), region(r)),
            Ty::PromptTag { answer, payload, effect, region: r } => Ty::PromptTag {
                answer: self.subst_memo(answer, map, memo),
                payload: self.subst_memo(payload, map, memo),
                effect: subst_effect(&effect, map),
                region: region(r),
            },
            Ty::Composable { arg, answer, effect, region: r } => Ty::Composable {
                arg: self.subst_memo(arg, map, memo),
                answer: self.subst_memo(answer, map, memo),
                effect: subst_effect(&effect, map),
                region: region(r),
            },
            Ty::MarkKey(t, r) => Ty::MarkKey(self.subst_memo(t, map, memo), region(r)),
            other => other,
        };
        let id = self.arena.ty(new);
        self.arena.set_link(slot, id);
        slot
    }
}

fn subst_effect(e: &Effect, map: &HashMap<DVar, D>) -> Effect {
    let mut out = Effect::pure();
    for a in &e.0 {
        let sub_r = |r: Region| match r {
            Region::Var(v) => match map.get(&v) {
                Some(D::Region(x)) => *x,
                _ => r,
            },
            c => c,
        };
        let piece = match *a {
            Atom::Var(v) => match map.get(&v) {
                Some(D::Effect(x)) => x.clone(),
                _ => Effect::atom(*a),
            },
            Atom::Read(r) => Effect::atom(Atom::Read(sub_r(r))),
            Atom::Write(r) => Effect::atom(Atom::Write(sub_r(r))),
            Atom::Alloc(r) => Effect::atom(Atom::Alloc(sub_r(r))),
            Atom::Goto(r) => Effect::atom(Atom::Goto(sub_r(r))),
            Atom::Comefrom(r) => Effect::atom(Atom::Comefrom(sub_r(r))),
        };
        out = out.union(&piece);
    }
    out
}

// ---------------------------------------------------------------- prompts
impl Checker {
    /// `(prompt tag body handler)`.
    ///
    /// The tag's type fixes what crosses the prompt: the body must produce
    /// the answer type `A`, the handler must take the payload `H` to an `A`,
    /// and the body's effect must be within the tag's bound `D` apart from
    /// control on the tag's region `R` — the bound is what a continuation
    /// captured up to this prompt is said to do when it is called.
    ///
    /// Then the prompt delimits: `(goto R)` and `(comefrom R)` are removed
    /// from the body's effect, but only if the body can reach no tag in `R`
    /// other than this one. A region can hold many tags, and an abort to
    /// another of them passes straight through this prompt. So the condition
    /// is on the body's free variables: none may have a type mentioning `R`,
    /// except the tag itself when `tag` is a variable. A tag the body makes
    /// for itself is fine: an abort to it with no prompt of its own inside
    /// the body is an error, not a jump past this one.
    fn synth_prompt(&mut self, e: ExpId, tag: ExpId, body: ExpId, handler: ExpId) -> R<(TyId, Effect)> {
        let (tt, te) = self.synth(tag)?;
        let Ty::PromptTag { answer, payload, effect: bound, region } = self.arena.get(tt).clone() else {
            return Err(FxError::at(
                self.arena.span_of(tag),
                format!("a prompt needs a prompt tag, not a {}", self.show_ty(tt)),
            ));
        };
        let (bt, be) = self.synth(body)?;
        if !self.subtype(bt, answer) {
            return Err(FxError::at(
                self.arena.span_of(body),
                format!("the tag's prompts deliver a {}, and this body is a {}", self.show_ty(answer), self.show_ty(bt)),
            ));
        }
        let own = Effect([Atom::Goto(region), Atom::Comefrom(region)].into_iter().collect());
        let beyond = Effect(be.0.iter().copied().filter(|a| !bound.contains(*a) && !own.contains(*a)).collect());
        if !beyond.is_pure() {
            return Err(FxError::at(
                self.arena.span_of(body),
                format!(
                    "the tag allows its delimited computations {}, and this body also has {}",
                    self.show_effect(&bound),
                    self.show_effect(&beyond)
                ),
            ));
        }
        let (ht, he) = self.synth(handler)?;
        let Some((latent, params, result)) = self.arena.get(ht).as_subr() else {
            return Err(FxError::at(self.arena.span_of(handler), format!("a handler is a subroutine, not a {}", self.show_ty(ht))));
        };
        if params.len() != 1 || !self.subtype(payload, params[0]) || !self.subtype(result, answer) {
            return Err(FxError::at(
                self.arena.span_of(handler),
                format!("the handler must take a {} to a {}; it is a {}", self.show_ty(payload), self.show_ty(answer), self.show_ty(ht)),
            ));
        }
        let delimited = if self.reaches_only(body, tag, region) {
            Effect(be.0.iter().copied().filter(|a| !own.contains(*a)).collect())
        } else {
            be
        };
        let eff = te.union(&he).union(&latent).union(&delimited);
        Ok((answer, self.mask(e, &eff, answer)))
    }

    /// Whether the only way `body` can name anything in region `r` is the
    /// variable `tag` (if `tag` is one).
    fn reaches_only(&self, body: ExpId, tag: ExpId, r: Region) -> bool {
        let tag_var = match self.arena.exp_at(tag) {
            Exp::Var(s) => Some(*s),
            _ => None,
        };
        self.free_vars(body).into_iter().filter(|v| Some(*v) != tag_var).all(|v| {
            let Some(t) = self.lookup(v) else { return true };
            let mut rs = HashSet::new();
            self.regions_in(t, &mut rs);
            !rs.contains(&r)
        })
    }
}
