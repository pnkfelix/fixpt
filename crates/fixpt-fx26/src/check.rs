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

use crate::ast::{Arena, Arm, ArmBind, Atom, BlobletOp, D, DVar, Effect, Exp, ExpId, Kind, Region, RegionForm, Ty, TyId};
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
    /// The region and place variables bound around what is being parsed,
    /// by expressions (not types): the order of lifetimes, by nesting.
    pub(crate) lifetimes: Vec<DVar>,
    /// The regions `letfreeze`s are freezing, innermost last, each with
    /// whether anything has written it: data never written is finite.
    pub(crate) freezing: Vec<(DVar, bool)>,
    /// Bindings of known procedures, by name and type: those a `define`,
    /// `letrec`, `define-rec`, or a `let` of a `lambda` made. A call of one
    /// runs code the checker has seen; a call of anything else might run a
    /// closure fetched from the store.
    pub(crate) known: HashSet<(Sym, TyId)>,
    /// The bindings of the recursive groups whose lambdas are being checked:
    /// a call of one of them there is recursion, and so `spin`.
    pub(crate) recursive: Vec<(Sym, TyId)>,
    pub(crate) base: HashMap<Sym, TyId>,
    pub(crate) void: TyId,
    pub(crate) int: TyId,
    bool_: TyId,
    string: TyId,
    unit: TyId,
    char_: TyId,
    symbol: TyId,
    /// How deep in abbreviation expansions parsing is, to stop one that
    /// mentions itself.
    pub(crate) expanding: u32,
    /// The type families being expanded, each with the descriptions given
    /// it and the slot its type will fill: a use inside with the same
    /// descriptions is that slot, a knot (regular recursion).
    pub(crate) knots: Vec<(Sym, Vec<crate::parse::FamilyArg>, TyId)>,
    /// How many fresh regions inference has made, for naming the next.
    pub(crate) fresh_regions: u32,
    /// How many entries of `env` are the initial environment's.
    pub(crate) standard_len: usize,
    /// What checking proved about each expression, for lowering to carry.
    pub facts: NodeFacts,
    /// The regions `private-regions` made this program's own.
    pub private_regions: Vec<Region>,
    /// Mask at every expression, as the rules say. Off only to observe an
    /// effect *before* masking, which is what some of the paper's claims are
    /// about.
    pub masking: bool,
}

/// What checking proved about expressions, keyed by expression. Lowering
/// turns these into `%fx-note` claims (`crate::lower`).
#[derive(Clone, Debug, Default)]
pub struct NodeFacts {
    /// Each expression's effect, after masking.
    pub effects: HashMap<ExpId, Effect>,
    /// Applications whose operator is a standard binding, by name. The
    /// initial environment cannot be assigned, so the operator is known.
    pub standard_operator: HashMap<ExpId, Sym>,
    /// Expressions that allocate, where masking removed every allocation:
    /// nothing they allocate outlives them.
    pub no_escape: HashSet<ExpId>,
    /// Each `extract`'s field, by position: lowering needs it, and only the
    /// product's type says it.
    pub field_index: HashMap<ExpId, usize>,
}

impl NodeFacts {
    /// Forget everything about expressions from `first` on.
    pub(crate) fn forget_from(&mut self, first: u32) {
        self.effects.retain(|e, _| e.0 < first);
        self.standard_operator.retain(|e, _| e.0 < first);
        self.no_escape.retain(|e| e.0 < first);
        self.field_index.retain(|e, _| e.0 < first);
    }
}

/// What checking an expression found.
#[derive(Clone, Debug)]
pub struct Checked {
    pub ty: TyId,
    pub effect: Effect,
    /// The expression checked, for lowering.
    pub exp: ExpId,
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
        let char_ = basic("char");
        // A Scheme datum, as a reader produces: opaque, and immutable, so
        // building one is no effect.
        basic("datum");
        // A symbol: interned, so compared by identity, and immutable.
        let symbol = basic("symbol");
        // Threaded code, for the compiler written in FX-26: a word (`tword`,
        // since the reader has a `word` of its own), a cell of one, and a
        // global's cell. Opaque; made by the `wcell-` and
        // `make-` constants and checked when a word is made.
        basic("tword");
        basic("wcell");
        basic("wglobal");
        let void = arena.ty(Ty::Void);
        let mut c = Checker {
            arena,
            interner,
            env: Vec::new(),
            dscope: Vec::new(),
            lifetimes: Vec::new(),
            freezing: Vec::new(),
            known: HashSet::new(),
            recursive: Vec::new(),
            base,
            void,
            int,
            bool_,
            string,
            unit,
            char_,
            symbol,
            expanding: 0,
            knots: Vec::new(),
            fresh_regions: 0,
            standard_len: 0,
            facts: NodeFacts::default(),
            private_regions: Vec::new(),
            masking: true,
        };
        for (name, ty) in crate::standard::ENTRIES {
            c.bind(name, ty).unwrap_or_else(|e| panic!("the standard type of `{name}` is wrong: {e}"));
        }
        c.standard_len = c.env.len();
        c
    }

    fn read(&mut self, text: &str) -> R<Vec<Syntax>> {
        let mut interner = std::mem::take(&mut self.interner);
        let r = Reader::new(text, fixpt_read::FileId(0), SyntaxProfile::FX26, &mut interner).read_all();
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
        Ok(Checked { ty, effect, exp: e })
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

    pub(crate) fn bool_ty(&self) -> TyId {
        self.bool_
    }

    pub(crate) fn lookup(&self, s: Sym) -> Option<TyId> {
        self.env.iter().rev().find(|(n, _)| *n == s).map(|(_, t)| *t)
    }

    // ------------------------------------------------------------ synthesis
    /// What `e` is, and what evaluating it does.
    pub fn synth(&mut self, e: ExpId) -> R<(TyId, Effect)> {
        let (t, eff) = self.synth_node(e)?;
        let eff = self.frozen(e, eff)?;
        self.facts.effects.insert(e, eff.clone());
        Ok((t, eff))
    }

    /// `eff` with what it does to frozen data taken out, since reading it
    /// and making it are pure; or an error, if it writes it.
    pub(crate) fn frozen(&self, e: ExpId, eff: Effect) -> R<Effect> {
        if !eff.0.iter().any(|a| a.region().is_some_and(Region::is_frozen)) {
            return Ok(eff);
        }
        if eff.0.iter().any(|a| matches!(a, Atom::Write(r) if r.is_frozen())) {
            return Err(FxError::at(self.arena.span_of(e), "this writes frozen data, whose region is `const`"));
        }
        Ok(Effect(eff.0.into_iter().filter(|a| !matches!(a, Atom::Read(r) | Atom::Alloc(r) | Atom::Await(r) if r.is_frozen())).collect()))
    }

    /// Whether `s`, where it is used, is the initial environment's binding.
    pub(crate) fn is_standard(&self, s: Sym) -> bool {
        self.env.iter().rposition(|(n, _)| *n == s).is_some_and(|i| i < self.standard_len)
    }

    fn synth_node(&mut self, e: ExpId) -> R<(TyId, Effect)> {
        let span = self.arena.span_of(e);
        match self.arena.exp_at(e).clone() {
            Exp::Var(s) => match self.lookup(s) {
                Some(t) => Ok((t, self.naming_effect(s, t))),
                None => Err(FxError::at(span, format!("unbound variable `{}`", self.interner.name(s)))),
            },
            Exp::Int(_) => Ok((self.int, Effect::pure())),
            Exp::Bool(_) => Ok((self.bool_, Effect::pure())),
            Exp::Str(_) => Ok((self.string, Effect::pure())),
            Exp::Char(_) => Ok((self.char_, Effect::pure())),
            Exp::Symbol(_) => Ok((self.symbol, Effect::pure())),
            Exp::Unit => Ok((self.unit, Effect::pure())),
            Exp::Lambda { .. } => self.synth_lambda(e, None),
            Exp::RLambda { region, lambda } => self.synth_rlambda(e, region, lambda, None),
            Exp::App { fun, args } => self.synth_app(e, fun, &args, None),
            Exp::The { ty, exp } => {
                let eff = self.check(exp, ty)?;
                Ok((ty, eff))
            }
            Exp::PLambda { binders, body } => {
                let (t, eff) = self.synth(body)?;
                if !self.generalizable(body, &eff) {
                    return Err(FxError::at(span, format!("a `plambda` body must be pure, and this one has {}", self.show_effect(&eff))));
                }
                Ok((self.arena.ty(Ty::Poly { binders, body: t }), eff))
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
                    let ok = match (k, &d) {
                        (Kind::Region, D::Region(_)) | (Kind::Effect, D::Effect(_)) | (Kind::Type, D::Type(_)) => true,
                        (Kind::Place, D::Region(r)) => self.arena.is_place(*r),
                        _ => false,
                    };
                    if !ok {
                        return Err(FxError::at(span, format!("`{}` is bound as a {k:?}, and the description given is not one", self.interner.name(self.arena.dvar_name(*v)))));
                    }
                    map.insert(*v, d);
                }
                self.check_bounds(&binders, &map, span)?;
                let result = self.subst(inner, &map);
                self.no_knot(result, span)?;
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
                self.known.extend(bindings.iter().map(|(n, t, _)| (*n, *t)));
                let rdepth = self.recursive.len();
                // Only lambdas: then nothing runs before every binding
                // exists, and no one sees the knot tied.
                if let Some((n, _, init)) = bindings.iter().find(|(_, _, init)| !self.is_lambda(*init)) {
                    self.env.truncate(depth);
                    return Err(FxError::at(self.arena.span_of(*init), letrec_not_lambda(self.interner.name(*n))));
                }
                // A group whose every run ends needs no `spin`.
                if !self.terminates(&bindings) {
                    self.recursive.extend(bindings.iter().map(|(n, t, _)| (*n, *t)));
                }
                let r = (|| {
                    let mut eff = Effect::pure();
                    for (n, t, init) in &bindings {
                        let ie = self.check(*init, *t).map_err(|err| {
                            if err.span == self.arena.span_of(*init) {
                                FxError::at(err.span, format!("`{}` is declared a {}: {}", self.interner.name(*n), self.show_ty(*t), err.message))
                            } else {
                                err
                            }
                        })?;
                        eff = eff.union(&ie);
                    }
                    // The body's calls of the group are not recursion.
                    self.recursive.truncate(rdepth);
                    let (bt, be) = self.synth(body)?;
                    Ok((bt, eff.union(&be)))
                })();
                self.recursive.truncate(rdepth);
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
                    if self.is_lambda(*init) {
                        self.known.insert((*n, t));
                    }
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
            // The region's name is a variable too, of type `(place r)`,
            // when the form makes a place: to allocate in (`rcons`).
            Exp::LetRegion { form, region, body } => {
                let name = self.arena.dvar_name(region);
                let rt = self.arena.ty(Ty::Place(Region::Var(region)));
                let depth = self.env.len();
                if !matches!(form, RegionForm::Region | RegionForm::Freeze(_)) {
                    self.env.push((name, rt));
                }
                if matches!(form, RegionForm::Freeze(_)) {
                    self.freezing.push((region, false));
                }
                let r = self.synth(body);
                let written = if matches!(form, RegionForm::Freeze(_)) { self.freezing.pop().expect("pushed").1 } else { true };
                self.env.truncate(depth);
                let (t, eff) = r?;
                // A `letfreeze`'s value leaves with its region's data frozen:
                // `r` made `const`, unless something in it could still write.
                let t = if let RegionForm::Freeze(into) = form {
                    if self.writes_in(t, Region::Var(region)) {
                        let name = self.interner.name(name);
                        return Err(FxError::at(span, format!("the value of `letfreeze {name}` could still write its region's data: its type is {}", self.show_ty(t))));
                    }
                    self.subst(t, &HashMap::from([(region, D::Region(Region::Frozen(into, !written)))]))
                } else {
                    t
                };
                self.close_region(e, form.keyword(), region, t, eff)
            }
            Exp::Bloblet { op, args } => self.synth_bloblet(e, op, &args, None),
            Exp::Product(fields) => {
                let mut eff = Effect::pure();
                let mut tys = Vec::new();
                for (l, x) in &fields {
                    let (t, xe) = self.synth(*x)?;
                    eff = eff.union(&xe);
                    tys.push((*l, t));
                }
                let t = self.arena.ty(Ty::Product(tys));
                let eff = self.mask(e, &eff, t);
                Ok((t, eff))
            }
            Exp::Extract(x, label) => {
                let (pt, eff) = self.synth(x)?;
                let Ty::Product(fields) = self.arena.get(pt).clone() else {
                    return Err(FxError::at(self.arena.span_of(x), format!("a product is expected here, and this is a {}", self.show_ty(pt))));
                };
                let Some(i) = fields.iter().position(|(l, _)| *l == label) else {
                    return Err(FxError::at(span, format!("a {} has no `{}`", self.show_ty(pt), self.interner.name(label))));
                };
                self.facts.field_index.insert(e, i);
                let t = fields[i].1;
                let eff = self.mask(e, &eff, t);
                Ok((t, eff))
            }
            Exp::Sum(tag, x) => {
                let (t, eff) = self.synth(x)?;
                let t = self.arena.ty(Ty::Sum(vec![(tag, t)]));
                let eff = self.mask(e, &eff, t);
                Ok((t, eff))
            }
            Exp::TagCase { scrutinee, arms, els } => self.synth_tagcase(e, scrutinee, &arms, &els, None),
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
    /// `(letrena r …)`'s or `(letreap r …)`'s body, of type `t` and effect
    /// `eff`, closed: its
    /// value may not mention `r`, and no continuation captured in it may
    /// outlive it; what it does to `r` is masked, as nothing outside can
    /// name `r`.
    pub(crate) fn close_region(&mut self, e: ExpId, form: &str, r: DVar, t: TyId, eff: Effect) -> R<(TyId, Effect)> {
        let span = self.arena.span_of(e);
        let name = self.interner.name(self.arena.dvar_name(r)).to_string();
        let mut in_t = HashSet::new();
        self.regions_in(t, &mut in_t);
        if in_t.contains(&Region::Var(r)) {
            return Err(FxError::at(span, region_escapes(form, &name, &self.show_ty(t))));
        }
        let masked = self.mask(e, &eff, t);
        if masked.0.iter().any(|a| matches!(a, Atom::Comefrom(_))) {
            return Err(FxError::at(span, region_captured(form, &name, &self.show_effect(&masked))));
        }
        Ok((t, masked))
    }

    /// Whether a `plambda` body `x` with effect `eff` may be generalized:
    /// pure, as the value restriction has it; or an `rlambda`, under
    /// ascriptions and other `plambda`s, whose effect only allocates. Making
    /// a closure makes no mutable data a type could be generalized over: it
    /// holds only variables bound outside.
    pub(crate) fn generalizable(&self, mut x: ExpId, eff: &Effect) -> bool {
        if eff.is_pure() {
            return true;
        }
        loop {
            match self.arena.exp_at(x) {
                Exp::PLambda { body, .. } | Exp::The { exp: body, .. } => x = *body,
                Exp::RLambda { .. } => return eff.0.iter().all(|a| matches!(a, Atom::Alloc(_))),
                _ => return false,
            }
        }
    }

    /// An `rlambda`'s type: its `lambda`'s, told `expected`'s parameter and
    /// result types if it is a subroutine's, with `(read R)` in its latent
    /// effect, since calling it reads the closure; making it allocates in
    /// `R`, the region `region` names.
    pub(crate) fn synth_rlambda(&mut self, e: ExpId, region: ExpId, lambda: ExpId, expected: Option<TyId>) -> R<(TyId, Effect)> {
        let (rt, reff) = self.synth(region)?;
        let Ty::Place(g) = self.arena.get(rt).clone() else {
            return Err(FxError::at(self.arena.span_of(region), format!("a region is expected here, and this is a {}", self.show_ty(rt))));
        };
        let hint = expected.and_then(|t| self.arena.get(t).as_subr());
        let (lt, _) = match hint {
            Some((_, want, result)) => {
                let Exp::Lambda { params, .. } = self.arena.exp_at(lambda) else { unreachable!("parsed") };
                if want.len() != params.len() {
                    let span = self.arena.span_of(e);
                    return Err(FxError::at(span, format!("a subroutine of {} parameter(s) is expected, and this `rlambda` has {}", want.len(), params.len())));
                }
                self.synth_lambda_as(lambda, Some(&want), Some(result))?
            }
            None => self.synth_lambda(lambda, None)?,
        };
        let Ty::Subr { mut effect, params, result } = self.arena.get(lt).clone() else { unreachable!("a lambda's type") };
        effect.0.insert(Atom::Read(g));
        let t = self.arena.ty(Ty::Subr { effect, params, result });
        let eff = reff.union(&Effect::atom(Atom::Alloc(g)));
        let eff = self.mask(e, &eff, t);
        Ok((t, eff))
    }

    /// Whether `x` is a lambda, under any type abstractions and ascriptions.
    /// Naming `s`: pure, but for a member of a recursive group that may not
    /// end, named in the group. Called, the call says `spin`; given away,
    /// whoever calls it could loop through it, so naming it does.
    pub(crate) fn naming_effect(&self, s: Sym, t: TyId) -> Effect {
        let mut e = Effect::pure();
        if self.recursive.contains(&(s, t)) {
            e.0.insert(Atom::Spin);
        }
        e
    }

    pub fn is_lambda(&self, mut x: ExpId) -> bool {
        loop {
            match self.arena.exp_at(x) {
                Exp::PLambda { body, .. } | Exp::The { exp: body, .. } => x = *body,
                Exp::Lambda { .. } | Exp::RLambda { .. } => return true,
                _ => return false,
            }
        }
    }

    pub(crate) fn mask(&mut self, e: ExpId, effect: &Effect, result: TyId) -> Effect {
        // A write to a region a `letfreeze` is freezing, noted before
        // masking could hide it: that region's data may be cyclic.
        for (v, written) in self.freezing.iter_mut() {
            if effect.0.contains(&Atom::Write(Region::Var(*v))) {
                *written = true;
            }
        }
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
                // What is done to frozen data is never masked: writing it is
                // an error wherever it happens (`frozen`).
                Some(Region::Frozen(..)) => true,
                Some(r) if visible.contains(&r) => true,
                Some(r) if in_result.contains(&r) => {
                    matches!(a, Atom::Alloc(_) | Atom::Goto(_) | Atom::Comefrom(_))
                }
                Some(_) => false,
            })
            .collect();
        let kept = Effect(kept);
        let allocates = |x: &Effect| x.0.iter().any(|a| matches!(a, Atom::Alloc(_)));
        if allocates(effect) && !allocates(&kept) {
            self.facts.no_escape.insert(e);
        }
        kept
    }

    /// The value variables free in `e`.
    pub(crate) fn free_vars(&self, e: ExpId) -> Vec<Sym> {
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
            Exp::Int(_) | Exp::Bool(_) | Exp::Str(_) | Exp::Char(_) | Exp::Symbol(_) | Exp::Unit => {}
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
            Exp::RLambda { region, lambda } => {
                self.free_into(region, bound, out);
                self.free_into(lambda, bound, out);
            }
            Exp::LetRegion { region, body, .. } => {
                bound.push(self.arena.dvar_name(region));
                self.free_into(body, bound, out);
                bound.pop();
            }
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
            Exp::The { exp, .. } => self.free_into(exp, bound, out),
            Exp::Bloblet { args, .. } => {
                for a in args {
                    self.free_into(a, bound, out);
                }
            }
            Exp::Product(fields) => {
                for (_, x) in fields {
                    self.free_into(x, bound, out);
                }
            }
            Exp::Extract(x, _) | Exp::Sum(_, x) => self.free_into(x, bound, out),
            Exp::TagCase { scrutinee, arms, els } => {
                self.free_into(scrutinee, bound, out);
                for arm in &arms {
                    let depth = bound.len();
                    bound.extend(arm.names());
                    self.free_into(arm.body, bound, out);
                    bound.truncate(depth);
                }
                if let Some((y, body)) = els {
                    bound.push(y);
                    self.free_into(body, bound, out);
                    bound.pop();
                }
            }
        }
    }

    /// Every region mentioned in type `t`, following recursive types once.
    pub fn regions_in(&self, t: TyId, out: &mut HashSet<Region>) {
        let mut seen = HashSet::new();
        self.regions_walk(t, &mut seen, out);
        // Frozen data mentions the place it is in.
        let places: Vec<Region> = out.iter().filter_map(|r| match r {
            Region::Frozen(Some(p), _) => Some(Region::Var(*p)),
            _ => None,
        }).collect();
        out.extend(places);
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
            Ty::Ref(a, r) | Ty::Array(a, r) | Ty::ICell(a, r) => {
                out.insert(r);
                self.regions_walk(a, seen, out);
            }
            Ty::Place(r) => {
                out.insert(r);
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
            Ty::Bloblet { fields, region, .. } => {
                out.insert(region);
                for f in fields {
                    self.regions_walk(f, seen, out);
                }
            }
            Ty::Product(parts) | Ty::Sum(parts) => {
                for (_, t) in parts {
                    self.regions_walk(t, seen, out);
                }
            }
        }
    }

    /// `Ok`, unless `t` keeps, in storage at some region `r`, a procedure
    /// whose latent effect reads or awaits `r` and does not say `spin`. Such
    /// a procedure could be fetched from `r` by a procedure fetched from
    /// `r`: a knot tied through the store, a loop with no recursive call,
    /// which only its type can show (`docs/research/type-and-effect-directions.md`,
    /// R6).
    pub(crate) fn no_knot(&self, t: TyId, span: fixpt_read::Span) -> R<()> {
        let mut seen = HashSet::new();
        match self.knot_in(t, &[], &mut seen) {
            None => Ok(()),
            Some((r, p)) => {
                let r = self.show_region(r);
                Err(FxError::at(
                    span,
                    format!("a procedure kept in `{r}` reads `{r}`, so it could reach itself: it must say `spin`, and it is a {}", self.show_ty(p)),
                ))
            }
        }
    }

    fn knot_in(&self, t: TyId, kept: &[Region], seen: &mut HashSet<(TyId, Vec<Region>)>) -> Option<(Region, TyId)> {
        let t = self.arena.resolve(t);
        if !seen.insert((t, kept.to_vec())) {
            return None;
        }
        let with = |r: Region| -> Vec<Region> {
            let mut k = kept.to_vec();
            if !k.contains(&r) {
                k.push(r);
            }
            k
        };
        let reads_kept = |e: &Effect| {
            if e.0.contains(&Atom::Spin) {
                return None;
            }
            e.0.iter().find_map(|a| match a {
                Atom::Read(r) | Atom::Await(r) if kept.contains(r) => Some(*r),
                _ => None,
            })
        };
        match self.arena.get(t).clone() {
            Ty::Ref(a, r) | Ty::Array(a, r) | Ty::ICell(a, r) | Ty::MarkKey(a, r) => self.knot_in(a, &with(r), seen),
            Ty::Pair(a, b, r) => {
                let k = if r.is_frozen() { kept.to_vec() } else { with(r) };
                self.knot_in(a, &k, seen).or_else(|| self.knot_in(b, &k, seen))
            }
            Ty::Bloblet { fields, frozen, region } => {
                let k = if frozen { kept.to_vec() } else { with(region) };
                fields.iter().find_map(|f| self.knot_in(*f, &k, seen))
            }
            Ty::Product(parts) | Ty::Sum(parts) => parts.iter().find_map(|(_, x)| self.knot_in(*x, kept, seen)),
            Ty::Poly { body, .. } => self.knot_in(body, kept, seen),
            // A procedure: kept where it is, it may not read there unsaid;
            // what it takes and gives is kept nowhere yet.
            Ty::Subr { effect, params, result } => reads_kept(&effect)
                .map(|r| (r, t))
                .or_else(|| params.iter().chain([&result]).find_map(|x| self.knot_in(*x, &[], seen))),
            Ty::Composable { arg, answer, effect, .. } => reads_kept(&effect)
                .map(|r| (r, t))
                .or_else(|| [arg, answer].iter().find_map(|x| self.knot_in(*x, &[], seen))),
            Ty::PromptTag { answer, payload, .. } => [answer, payload].iter().find_map(|x| self.knot_in(*x, &[], seen)),
            _ => None,
        }
    }

    /// Whether a latent effect anywhere in `t` writes `r`: what a
    /// `letfreeze`'s value may not do to its region.
    pub(crate) fn writes_in(&self, t: TyId, r: Region) -> bool {
        let mut seen = HashSet::new();
        let mut todo = vec![t];
        while let Some(t) = todo.pop() {
            let t = self.arena.resolve(t);
            if !seen.insert(t) {
                continue;
            }
            let (effects, kids): (Vec<&Effect>, Vec<TyId>) = match self.arena.get(t) {
                Ty::Subr { effect, params, result } => (vec![effect], params.iter().copied().chain([*result]).collect()),
                Ty::PromptTag { answer, payload, effect, .. } => (vec![effect], vec![*answer, *payload]),
                Ty::Composable { arg, answer, effect, .. } => (vec![effect], vec![*arg, *answer]),
                Ty::Poly { body, .. } => (vec![], vec![*body]),
                Ty::Ref(a, _) | Ty::Array(a, _) | Ty::ICell(a, _) | Ty::MarkKey(a, _) => (vec![], vec![*a]),
                Ty::Pair(a, b, _) => (vec![], vec![*a, *b]),
                Ty::Bloblet { fields, .. } => (vec![], fields.clone()),
                Ty::Product(parts) | Ty::Sum(parts) => (vec![], parts.iter().map(|(_, t)| *t).collect()),
                _ => (vec![], vec![]),
            };
            if effects.iter().any(|e| e.0.contains(&Atom::Write(r))) {
                return true;
            }
            todo.extend(kids);
        }
        false
    }

    // ------------------------------------------------------------- subtyping
    /// `a ≤ b`. Recursive types are compared coinductively: a pair already
    /// being compared is assumed to hold, which is what makes comparing two
    /// cycles terminate — FX-87's `trail`, Amadio and Cardelli's assumption
    /// set. Every rule is a conjunction, so an assumption left behind by a
    /// comparison that failed is never relied on: the failure is the answer.
    pub fn subtype(&mut self, a: TyId, b: TyId) -> bool {
        let mut st = SubState::default();
        self.sub(a, b, &BinderEnv::default(), &mut st)
    }

    /// `a ≤ b` under `env`, which names each `poly` binder in scope on either
    /// side by the pair of `poly` nodes that bound it, so their bodies are
    /// compared as they are, not substituted: a cycle through a `poly` comes
    /// back to a pair, and an environment, already on the trail.
    fn sub(&mut self, a: TyId, b: TyId, env: &BinderEnv, st: &mut SubState) -> bool {
        let (a, b) = (self.arena.resolve(a), self.arena.resolve(b));
        if (a == b && env.is_empty()) || !st.trail.insert((a, b, env.clone())) {
            return true;
        }
        let (ta, tb) = (self.arena.get(a).clone(), self.arena.get(b).clone());
        let ra = |r: Region| env.region(&env.a, r);
        let rb = |r: Region| env.region(&env.b, r);
        let ea = |e: &Effect| env.effect(&env.a, e);
        let eb = |e: &Effect| env.effect(&env.b, e);
        let flip = env.flip();
        // A composable continuation can be called, so it can stand where a
        // subroutine is wanted.
        if let (Ty::Composable { .. }, Ty::Subr { .. }) = (&ta, &tb) {
            let (xa, pa, qa) = ta.as_subr().expect("callable");
            let (xb, pb, qb) = tb.as_subr().expect("callable");
            return pa.len() == pb.len()
                && ea(&xa).within(&eb(&xb))
                && pa.iter().zip(&pb).all(|(x, y)| self.sub(*y, *x, &flip, st))
                && self.sub(qa, qb, env, st);
        }
        match (ta, tb) {
            // `void` is the bottom type: nothing is ever returned as one.
            (Ty::Void, _) => true,
            (Ty::Base(x), Ty::Base(y)) => x == y,
            (Ty::Var(x), Ty::Var(y)) => env.var(&env.a, x) == env.var(&env.b, y),
            (
                Ty::Subr { effect: xa, params: pa, result: qa },
                Ty::Subr { effect: xb, params: pb, result: qb },
            ) => {
                pa.len() == pb.len()
                    && ea(&xa).within(&eb(&xb))
                    && pa.iter().zip(&pb).all(|(x, y)| self.sub(*y, *x, &flip, st))
                    && self.sub(qa, qb, env, st)
            }
            // References and pairs are mutable, so their contents are
            // invariant: FX-87's `ref` rule, and its pairs.
            (Ty::Place(r), Ty::Place(s)) => ra(r) == rb(s),
            (Ty::Ref(x, r), Ty::Ref(y, s)) | (Ty::Array(x, r), Ty::Array(y, s)) | (Ty::ICell(x, r), Ty::ICell(y, s)) => {
                ra(r) == rb(s) && self.sub(x, y, env, st) && self.sub(y, x, &flip, st)
            }
            // Frozen pairs cannot be written, so, as a frozen bloblet's
            // fields, their contents are covariant.
            (Ty::Pair(x1, x2, r), Ty::Pair(y1, y2, s)) if r.is_frozen() && Region::frozen_le(ra(r), rb(s)) => {
                self.sub(x1, y1, env, st) && self.sub(x2, y2, env, st)
            }
            (Ty::Pair(x1, x2, r), Ty::Pair(y1, y2, s)) => {
                ra(r) == rb(s)
                    && self.sub(x1, y1, env, st)
                    && self.sub(y1, x1, &flip, st)
                    && self.sub(x2, y2, env, st)
                    && self.sub(y2, x2, &flip, st)
            }
            // A tag both delivers and receives values of its types, so it is
            // invariant in all of them, as a reference is in its contents.
            (
                Ty::PromptTag { answer: a1, payload: h1, effect: d1, region: r1 },
                Ty::PromptTag { answer: a2, payload: h2, effect: d2, region: r2 },
            ) => {
                ra(r1) == rb(r2)
                    && ea(&d1) == eb(&d2)
                    && self.sub(a1, a2, env, st)
                    && self.sub(a2, a1, &flip, st)
                    && self.sub(h1, h2, env, st)
                    && self.sub(h2, h1, &flip, st)
            }
            // Called like a subroutine: contravariant in what it takes,
            // covariant in what it gives and does.
            (
                Ty::Composable { arg: t1, answer: a1, effect: d1, region: r1 },
                Ty::Composable { arg: t2, answer: a2, effect: d2, region: r2 },
            ) => ra(r1) == rb(r2) && ea(&d1).within(&eb(&d2)) && self.sub(t2, t1, &flip, st) && self.sub(a1, a2, env, st),
            (Ty::MarkKey(x, r), Ty::MarkKey(y, s)) => ra(r) == rb(s) && self.sub(x, y, env, st) && self.sub(y, x, &flip, st),
            // A bloblet's fields are invariant, as a reference's contents
            // are, unless they are frozen, when nothing can store into them.
            // Freezing is a change of type, never a subtype: a bloblet seen
            // as frozen through one name could still be written through
            // another.
            (
                Ty::Bloblet { fields: fa, frozen: za, region: r },
                Ty::Bloblet { fields: fb, frozen: zb, region: s },
            ) => {
                (ra(r) == rb(s) || (za && Region::frozen_le(ra(r), rb(s))))
                    && za == zb
                    && fa.len() == fb.len()
                    && fa.iter().zip(&fb).all(|(x, y)| self.sub(*x, *y, env, st) && (za || self.sub(*y, *x, &flip, st)))
            }
            // Immutable, so covariant: a product in its fields, a sum in its
            // variants, and a sum with fewer tags fits one with more.
            (Ty::Product(pa), Ty::Product(pb)) => {
                pa.len() == pb.len() && pa.iter().zip(&pb).all(|((la, x), (lb, y))| la == lb && self.sub(*x, *y, env, st))
            }
            (Ty::Sum(sa), Ty::Sum(sb)) => sa.iter().all(|(la, x)| {
                sb.iter().find(|(lb, _)| lb == la).is_some_and(|(_, y)| self.sub(*x, *y, env, st))
            }),
            (Ty::Poly { binders: ba, body: xa }, Ty::Poly { binders: bb, body: xb }) => {
                if ba.len() != bb.len() || ba.iter().zip(&bb).any(|((_, k1), (_, k2))| k1 != k2) {
                    return false;
                }
                // Each pair of binders is named by the pair of nodes and its
                // position: entering the same pair again rebinds the same
                // name, as re-entering a scope shadows it, so the
                // environments stay finitely many.
                let mut inner = env.clone();
                for (i, ((va, _), (vb, _))) in ba.iter().zip(&bb).enumerate() {
                    let n = st.labels.len() as u32;
                    let l = *st.labels.entry((a, b, i)).or_insert(DVar(u32::MAX - n));
                    inner.a.insert(*va, l);
                    inner.b.insert(*vb, l);
                }
                // Bounded region binders must have the same bounds.
                let bounds = ba.iter().zip(&bb).all(|((va, _), (vb, _))| {
                    match (self.arena.bound(*va), self.arena.bound(*vb)) {
                        (None, None) => true,
                        (Some(x), Some(y)) => inner.region(&inner.a, x) == inner.region(&inner.b, y),
                        _ => false,
                    }
                });
                bounds && self.sub(xa, xb, &inner, st)
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
        let region = |r: Region| subst_region(r, map);
        let new = match ty {
            Ty::Subr { effect, params, result } => {
                let effect = subst_effect(&effect, map);
                let params = params.iter().map(|p| self.subst_memo(*p, map, memo)).collect();
                let result = self.subst_memo(result, map, memo);
                Ty::Subr { effect, params, result }
            }
            Ty::Poly { binders, body } => Ty::Poly { binders, body: self.subst_memo(body, map, memo) },
            Ty::Ref(a, r) => Ty::Ref(self.subst_memo(a, map, memo), region(r)),
            Ty::Array(a, r) => Ty::Array(self.subst_memo(a, map, memo), region(r)),
            Ty::ICell(a, r) => Ty::ICell(self.subst_memo(a, map, memo), region(r)),
            Ty::Place(r) => Ty::Place(region(r)),
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
            Ty::Product(parts) => Ty::Product(parts.iter().map(|(l, t)| (*l, self.subst_memo(*t, map, memo))).collect()),
            Ty::Sum(parts) => Ty::Sum(parts.iter().map(|(l, t)| (*l, self.subst_memo(*t, map, memo))).collect()),
            Ty::Bloblet { fields, frozen, region: r } => Ty::Bloblet {
                fields: fields.iter().map(|f| self.subst_memo(*f, map, memo)).collect(),
                frozen,
                region: region(r),
            },
            other => other,
        };
        let id = self.arena.ty(new);
        self.arena.set_link(slot, id);
        slot
    }
}

/// `r` with `map`'s regions for its variables: frozen data's place too.
pub(crate) fn subst_region(r: Region, map: &HashMap<DVar, D>) -> Region {
    match r {
        Region::Var(v) => match map.get(&v) {
            Some(D::Region(x)) => *x,
            _ => r,
        },
        Region::Frozen(Some(p), f) => match map.get(&p) {
            Some(D::Region(Region::Var(q))) => Region::Frozen(Some(*q), f),
            Some(D::Region(Region::Heap)) => Region::Frozen(None, f),
            _ => r,
        },
        c => c,
    }
}

fn subst_effect(e: &Effect, map: &HashMap<DVar, D>) -> Effect {
    let mut out = Effect::pure();
    for a in &e.0 {
        let sub_r = |r: Region| subst_region(r, map);
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
            Atom::Await(r) => Effect::atom(Atom::Await(sub_r(r))),
            Atom::Spin => Effect::atom(Atom::Spin),
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
    // ------------------------------------------------------------- tagcase
    /// `tagcase`. `expected`, when checking, is what every arm is checked
    /// against; otherwise the result is the arms' types' least upper bound
    /// among themselves.
    pub(crate) fn synth_tagcase(
        &mut self,
        e: ExpId,
        scrutinee: ExpId,
        arms: &[Arm],
        els: &Option<(Sym, ExpId)>,
        expected: Option<TyId>,
    ) -> R<(TyId, Effect)> {
        let span = self.arena.span_of(e);
        let (st, mut eff) = self.synth(scrutinee)?;
        let Ty::Sum(variants) = self.arena.get(st).clone() else {
            return Err(FxError::at(self.arena.span_of(scrutinee), format!("a sum is expected here, and this is a {}", self.show_ty(st))));
        };
        let mut types = Vec::new();
        for arm in arms {
            let Some((_, t)) = variants.iter().find(|(l, _)| *l == arm.tag) else {
                return Err(FxError::at(self.arena.span_of(arm.body), format!("a {} has no tag `{}`", self.show_ty(st), self.interner.name(arm.tag))));
            };
            let bound: Vec<(Sym, TyId)> = match &arm.bind {
                ArmBind::Value(x) => vec![(*x, *t)],
                ArmBind::Fields(xs) => match self.arena.get(*t).clone() {
                    Ty::Product(fs) if fs.len() == xs.len() => xs.iter().zip(&fs).map(|(x, (_, t))| (*x, *t)).collect(),
                    _ => {
                        return Err(FxError::at(self.arena.span_of(arm.body), format!("`{}` carries a {}, which cannot be taken apart into {} name(s)", self.interner.name(arm.tag), self.show_ty(*t), xs.len())));
                    }
                },
            };
            let (t, be) = self.in_scope(&bound, |c| match expected {
                Some(x) => Ok((x, c.check(arm.body, x)?)),
                None => c.synth(arm.body),
            })?;
            eff = eff.union(&be);
            types.push(t);
        }
        let rest: Vec<(Sym, TyId)> = variants.iter().filter(|(l, _)| !arms.iter().any(|a| a.tag == *l)).cloned().collect();
        match els {
            Some((y, body)) => {
                let rest_ty = self.arena.ty(Ty::Sum(rest));
                let (t, be) = self.in_scope(&[(*y, rest_ty)], |c| match expected {
                    Some(x) => Ok((x, c.check(*body, x)?)),
                    None => c.synth(*body),
                })?;
                eff = eff.union(&be);
                types.push(t);
            }
            None if !rest.is_empty() => {
                let names: Vec<&str> = rest.iter().map(|(l, _)| self.interner.name(*l)).collect();
                return Err(FxError::at(span, format!("this `tagcase` has no arm for {}", names.join(", "))));
            }
            None => {}
        }
        let t = match expected {
            Some(x) => x,
            None => {
                let Some(t) = types.iter().copied().find(|t| types.clone().iter().all(|u| self.subtype(*u, *t))) else {
                    let shown: Vec<String> = types.iter().map(|t| self.show_ty(*t)).collect();
                    return Err(FxError::at(span, format!("the arms are {}", shown.join(", "))));
                };
                t
            }
        };
        let eff = self.mask(e, &eff, t);
        Ok((t, eff))
    }

    /// Run `f` with `bound` in scope.
    fn in_scope<T>(&mut self, bound: &[(Sym, TyId)], f: impl FnOnce(&mut Self) -> R<T>) -> R<T> {
        let depth = self.env.len();
        self.env.extend_from_slice(bound);
        let r = f(self);
        self.env.truncate(depth);
        r
    }

    // --------------------------------------------------------------- bloblets
    /// The bloblet forms. `expected`, when checking, supplies a new
    /// bloblet's region and field types.
    pub(crate) fn synth_bloblet(
        &mut self,
        e: ExpId,
        op: BlobletOp,
        args: &[ExpId],
        expected: Option<TyId>,
    ) -> R<(TyId, Effect)> {
        let span = self.arena.span_of(e);
        let int = self.int;
        if matches!(op, BlobletOp::Make | BlobletOp::RMake) {
            // `rmake-bloblet`'s region is its first operand's; `make-bloblet`'s
            // the type it is checked against, or a fresh one.
            let (given, mut eff, args) = if op == BlobletOp::RMake {
                let (r, rest) = args.split_first().expect("parsed");
                let (rt, re) = self.synth(*r)?;
                let Ty::Place(g) = self.arena.get(rt).clone() else {
                    return Err(FxError::at(span, format!("a region is expected here, and this is a {}", self.show_ty(rt))));
                };
                (Some(g), re, rest)
            } else {
                (None, Effect::pure(), args)
            };
            let (bytes, fields) = args.split_first().expect("parsed");
            eff = eff.union(&self.check(*bytes, int)?);
            let want = expected.and_then(|t| match self.arena.get(t).clone() {
                Ty::Bloblet { fields: fs, frozen: false, region }
                    if fs.len() == fields.len() && given.is_none_or(|g| g == region) =>
                {
                    Some((fs, region))
                }
                _ => None,
            });
            let (tys, region) = match want {
                Some((fs, region)) => {
                    for (f, t) in fields.iter().zip(&fs) {
                        eff = eff.union(&self.check(*f, *t)?);
                    }
                    (fs, region)
                }
                None => {
                    let mut tys = Vec::new();
                    for f in fields {
                        let (t, fe) = self.synth(*f)?;
                        eff = eff.union(&fe);
                        tys.push(t);
                    }
                    (tys, given.unwrap_or_else(|| self.fresh_region_named("bloblet")))
                }
            };
            eff.0.insert(Atom::Alloc(region));
            let t = self.arena.ty(Ty::Bloblet { fields: tys, frozen: false, region });
            self.no_knot(t, span)?;
            let eff = self.mask(e, &eff, t);
            return Ok((t, eff));
        }
        let (b, rest) = args.split_first().expect("parsed");
        let (bt, mut eff) = self.synth(*b)?;
        let Ty::Bloblet { fields, frozen, region } = self.arena.get(bt).clone() else {
            return Err(FxError::at(self.arena.span_of(*b), format!("a bloblet is expected here, and this is a {}", self.show_ty(bt))));
        };
        let field = |c: &Self, i: usize| -> R<TyId> {
            fields.get(i).copied().ok_or_else(|| {
                FxError::at(span, format!("a {} has no field {i}: its fields are 0 to {}", c.show_ty(bt), fields.len() as i64 - 1))
            })
        };
        let t = match op {
            BlobletOp::Make | BlobletOp::RMake => unreachable!(),
            BlobletOp::Ref(i) => {
                let t = field(self, i)?;
                if !frozen {
                    eff.0.insert(Atom::Read(region));
                }
                t
            }
            BlobletOp::Set(i) => {
                let t = field(self, i)?;
                if frozen {
                    return Err(FxError::at(span, format!("a {} cannot be changed: its fields are frozen", self.show_ty(bt))));
                }
                eff = eff.union(&self.check(rest[0], t)?);
                eff.0.insert(Atom::Write(region));
                self.unit
            }
            BlobletOp::Freeze => {
                eff.0.insert(Atom::Write(region));
                self.arena.ty(Ty::Bloblet { fields: fields.clone(), frozen: true, region })
            }
            BlobletOp::Byte => {
                eff = eff.union(&self.check(rest[0], int)?);
                eff.0.insert(Atom::Read(region));
                int
            }
            BlobletOp::SetByte => {
                eff = eff.union(&self.check(rest[0], int)?);
                eff = eff.union(&self.check(rest[1], int)?);
                eff.0.insert(Atom::Write(region));
                self.unit
            }
            // The suffix's length never changes.
            BlobletOp::Bytes => int,
        };
        let eff = self.mask(e, &eff, t);
        Ok((t, eff))
    }

    fn synth_prompt(&mut self, e: ExpId, tag: ExpId, body: ExpId, handler: ExpId) -> R<(TyId, Effect)> {
        let (tt, te) = self.synth(tag)?;
        let Ty::PromptTag { answer, payload, effect: bound, region } = self.arena.get(tt).clone() else {
            return Err(FxError::at(
                self.arena.span_of(tag),
                format!("a prompt needs a prompt tag, not a {}", self.show_ty(tt)),
            ));
        };
        // Checked against the answer type, so that what the body needs to
        // know — an operator's binders, a `nil` — it is told.
        let be = self.check(body, answer).map_err(|err| {
            match err.message.strip_prefix("a ").and_then(|m| m.split_once(" is expected here, and this is a ")) {
                Some((want, got)) if err.span == self.arena.span_of(body) => FxError::at(
                    err.span,
                    format!("the tag's prompts deliver a {want}, and this body is a {got}"),
                ),
                _ => err,
            }
        })?;
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
        // A handler written as a `lambda` is told what it takes and gives.
        let (ht, he) = if matches!(self.arena.exp_at(handler), Exp::Lambda { params, .. } if params.len() == 1) {
            let Exp::Lambda { body: hbody, .. } = self.arena.exp_at(handler).clone() else { unreachable!() };
            self.synth_lambda_as(handler, Some(&[payload]), Some(answer)).map_err(|err| {
                match err.message.strip_prefix("a ").and_then(|m| m.split_once(" is expected here, and this is a ")) {
                    Some((_, got)) if err.span == self.arena.span_of(hbody) => FxError::at(
                        err.span,
                        format!(
                            "the handler must take a {} to a {}, and this gives a {got}",
                            self.show_ty(payload),
                            self.show_ty(answer)
                        ),
                    ),
                    _ => err,
                }
            })?
        } else {
            self.synth(handler)?
        };
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

/// What a recursive binding that is not a lambda is told.
pub fn letrec_not_lambda(name: &str) -> String {
    format!("`{name}` is bound recursively, so it must be a lambda: nothing may run before every binding exists")
}

/// What a `letrena` or `letreap` whose value would outlive its region is
/// told.
pub fn region_escapes(form: &str, r: &str, t: &str) -> String {
    format!("the value of `{form} {r}` would outlive its region: its type is {t}")
}

/// What one whose body may capture a continuation is told.
pub fn region_captured(form: &str, r: &str, eff: &str) -> String {
    format!("a continuation captured in `{form} {r}` could outlive its region: its effect is {eff}")
}

/// What one subtype question remembers: the pairs assumed (FX-87's trail),
/// each with the binder environment it was asked under, and the names given
/// to pairs of `poly` binders.
#[derive(Default)]
struct SubState {
    trail: HashSet<(TyId, TyId, BinderEnv)>,
    labels: HashMap<(TyId, TyId, usize), DVar>,
}

/// For each side of a subtype question, the `poly` binders in scope, each
/// mapped to the name its pair of binders was given.
#[derive(Clone, Default, PartialEq, Eq, Hash)]
struct BinderEnv {
    a: std::collections::BTreeMap<DVar, DVar>,
    b: std::collections::BTreeMap<DVar, DVar>,
}

impl BinderEnv {
    fn is_empty(&self) -> bool {
        self.a.is_empty() && self.b.is_empty()
    }
    /// The same environment, for the question asked the other way round.
    fn flip(&self) -> BinderEnv {
        BinderEnv { a: self.b.clone(), b: self.a.clone() }
    }
    fn var(&self, side: &std::collections::BTreeMap<DVar, DVar>, v: DVar) -> DVar {
        side.get(&v).copied().unwrap_or(v)
    }
    fn region(&self, side: &std::collections::BTreeMap<DVar, DVar>, r: Region) -> Region {
        match r {
            Region::Var(v) => Region::Var(self.var(side, v)),
            Region::Frozen(Some(p), f) => Region::Frozen(Some(self.var(side, p)), f),
            c => c,
        }
    }
    fn effect(&self, side: &std::collections::BTreeMap<DVar, DVar>, e: &Effect) -> Effect {
        if side.is_empty() {
            return e.clone();
        }
        let r = |x: Region| self.region(side, x);
        Effect(
            e.0.iter()
                .map(|a| match *a {
                    Atom::Var(v) => Atom::Var(self.var(side, v)),
                    Atom::Read(x) => Atom::Read(r(x)),
                    Atom::Write(x) => Atom::Write(r(x)),
                    Atom::Alloc(x) => Atom::Alloc(r(x)),
                    Atom::Goto(x) => Atom::Goto(r(x)),
                    Atom::Comefrom(x) => Atom::Comefrom(r(x)),
                    Atom::Await(x) => Atom::Await(r(x)),
                    Atom::Spin => Atom::Spin,
                })
                .collect(),
        )
    }
}
