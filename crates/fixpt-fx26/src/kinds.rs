//! Higher kinds (`docs/research/higher-kinds.md`): description functions,
//! of arrow kinds `(=> (k1 … kn) k)`, made by `dlambda` and applied to
//! descriptions. FX-91's `(->> k1 … kn)` and `dlambda`, with the result of
//! any kind, not only a type.
//!
//! A description function is a [`Ty::Lam`], a variable of an arrow kind,
//! or a `select` of a module's component; it is carried as a [`D::Fun`].
//! Applying a `Lam` substitutes what it is given for its parameters (beta);
//! a `Lam` that only applies a function to its parameters is that function
//! (eta). What cannot be reduced, a variable applied, is a [`Ty::App`],
//! equal only to an application of the same function to equal descriptions.
//! Nothing is solved for: a function variable is matched only against an
//! application of a function (`infer.rs`), never against an arbitrary type,
//! as FX-91 and Jones's constructor classes keep it decidable.

use crate::ast::{D, DVar, Effect, Kind, Region, Size, Ty, TyId};
use crate::check::Checker;
use crate::error::{FxError, R};
use crate::parse::DScope;
use fixpt_read::{Sym, Syntax};
use std::collections::HashMap;

/// What an effect function is given, of a description; none for a type.
fn d_earg(d: D) -> Option<crate::ast::EArg> {
    use crate::ast::EArg;
    match d {
        D::Region(r) => Some(EArg::Region(r)),
        D::Effect(e) => Some(EArg::Effect(e)),
        D::Size(z) => Some(EArg::Size(z)),
        D::Conv(c) => Some(EArg::Conv(c)),
        D::Type(_) | D::Fun(_) => None,
    }
}

/// The type forms that are also description functions when written alone,
/// `listof` for `(dlambda ((t type) (r region)) (listof t r))`: each with
/// its parameters' names and kinds.
pub(crate) const CONSTRUCTORS: &[(&str, &[(&str, Kind)])] = &[
    ("ref", &[("t", Kind::Type), ("r", Kind::Region)]),
    ("icell", &[("t", Kind::Type), ("r", Kind::Region)]),
    ("pairof", &[("a", Kind::Type), ("b", Kind::Type), ("r", Kind::Region)]),
    ("listof", &[("t", Kind::Type), ("r", Kind::Region)]),
    ("arrayof", &[("t", Kind::Type), ("r", Kind::Region)]),
    ("mark-key", &[("t", Kind::Type), ("r", Kind::Region)]),
];

impl Checker {
    /// A kind as it is written: `type`, or `(=> (type) type)`.
    pub(crate) fn show_kind(&self, k: Kind) -> String {
        match k {
            Kind::Region => "region".into(),
            Kind::Place => "place".into(),
            Kind::Effect => "effect".into(),
            Kind::Type => "type".into(),
            Kind::Data => "data".into(),
            Kind::Size => "size".into(),
            Kind::Conv => "conv".into(),
            Kind::Arrow(_) => {
                let (params, result) = self.arena.arrow_parts(k).expect("an arrow");
                let ps: Vec<String> = params.iter().map(|p| self.show_kind(*p)).collect();
                format!("(=> ({}) {})", ps.join(" "), self.show_kind(result))
            }
        }
    }

    /// A kind as the older messages name it: `Region`, `Type`, …; an arrow
    /// kind as it is written.
    pub(crate) fn kind_word(&self, k: Kind) -> String {
        match k {
            Kind::Arrow(_) => self.show_kind(k),
            k => format!("{k:?}"),
        }
    }

    /// The kind of description function `f`, where it is known: not for a
    /// `select` not yet resolved.
    pub(crate) fn fun_kind(&mut self, f: TyId) -> Option<Kind> {
        match self.arena.get(f).clone() {
            Ty::Var(v) => self.arena.dvar_kind_known(v),
            Ty::Lam { params, body } => {
                let result = self.d_kind(&body)?;
                Some(self.arena.arrow(params.iter().map(|(_, k)| *k).collect(), result))
            }
            // A function that gives a function, applied.
            Ty::App { fun, .. } => self.fun_kind(fun).and_then(|k| self.arena.arrow_parts(k).map(|(_, r)| r)),
            _ => None,
        }
    }

    /// The kind a description is of, where it is known.
    pub(crate) fn d_kind(&mut self, d: &D) -> Option<Kind> {
        match d {
            D::Region(r) => Some(if self.arena.is_place(*r) { Kind::Place } else { Kind::Region }),
            D::Effect(_) => Some(Kind::Effect),
            D::Type(_) => Some(Kind::Type),
            D::Size(_) => Some(Kind::Size),
            D::Conv(_) => Some(Kind::Conv),
            D::Fun(f) => self.fun_kind(*f),
        }
    }

    /// Whether description `d` may stand where one of kind `k` is wanted
    /// (a `data` type is confirmed apart, as a `proj`'s is). A function
    /// whose kind is not known yet, a `select`, is let through, and is
    /// checked once it is resolved.
    pub(crate) fn d_fits(&mut self, d: &D, k: Kind) -> bool {
        match (k, d) {
            (Kind::Region, D::Region(_)) | (Kind::Effect, D::Effect(_)) | (Kind::Type | Kind::Data, D::Type(_)) => true,
            (Kind::Size, D::Size(_)) | (Kind::Conv, D::Conv(_)) => true,
            (Kind::Place, D::Region(r)) => self.arena.is_place(*r),
            (Kind::Arrow(_), D::Fun(f)) => self.fun_kind(*f).is_none_or(|got| got == k),
            _ => false,
        }
    }

    /// `(dlambda params body)`, or, where `body` only applies a function
    /// to the parameters in order, that function (eta).
    pub(crate) fn lam(&mut self, params: Vec<(DVar, Kind)>, body: D) -> TyId {
        if let D::Type(t) = &body
            && let Ty::App { fun, args } = self.arena.get(*t).clone()
            && args.len() == params.len()
            && args.iter().zip(&params).all(|(a, (p, _))| self.is_the_var(a, *p))
            && !matches!(self.arena.get(fun), Ty::Var(v) if params.iter().any(|(p, _)| p == v))
        {
            return fun;
        }
        self.arena.ty(Ty::Lam { params, body })
    }

    /// Whether `d` is variable `v` and nothing more.
    fn is_the_var(&self, d: &D, v: DVar) -> bool {
        match d {
            D::Region(Region::Var(w)) => *w == v,
            D::Effect(e) => e.0.len() == 1 && e.0.contains(&crate::ast::Atom::Var(v)),
            D::Size(Size::Lin { k: 0, terms }) => terms[..] == [(v, 1)],
            D::Conv(crate::ast::Conv::Var(w)) => *w == v,
            D::Type(t) | D::Fun(t) => matches!(self.arena.get(*t), Ty::Var(w) if *w == v),
            _ => false,
        }
    }

    /// Function `f` applied to `args`: what a `dlambda` reduces to, or an
    /// application that cannot be reduced. `args` fit `f`'s kind, which the
    /// caller has made sure of.
    pub(crate) fn apply_fun(&mut self, f: TyId, args: Vec<D>) -> D {
        match self.arena.get(f).clone() {
            Ty::Lam { params, body } if params.len() == args.len() => {
                let map: HashMap<DVar, D> = params.iter().map(|(v, _)| *v).zip(args).collect();
                self.subst_d(&body, &map)
            }
            // Stuck: an effect, an atom of its own; a function; or a type.
            _ => match self.fun_kind(f).and_then(|k| self.arena.arrow_parts(k).map(|(_, r)| r)) {
                Some(Kind::Effect) => match self.arena.get(f).clone() {
                    Ty::Var(v) => {
                        let args = args.into_iter().filter_map(d_earg).collect();
                        D::Effect(Effect::atom(self.arena.effect_apps.atom(v, args)))
                    }
                    _ => D::Effect(Effect::pure()),
                },
                Some(Kind::Arrow(_)) => D::Fun(self.arena.ty(Ty::App { fun: f, args })),
                _ => D::Type(self.arena.ty(Ty::App { fun: f, args })),
            },
        }
    }

    /// A description substituted into: `map`'s descriptions for its
    /// variables.
    pub(crate) fn subst_d(&mut self, d: &D, map: &HashMap<DVar, D>) -> D {
        match d {
            D::Type(t) => D::Type(self.subst(*t, map)),
            D::Fun(f) => D::Fun(self.subst(*f, map)),
            D::Region(r) => D::Region(crate::check::subst_region(*r, map)),
            D::Effect(e) => D::Effect(crate::check::subst_effect(e, map, &self.arena)),
            D::Size(z) => D::Size(crate::sizes::subst_size(z, map)),
            D::Conv(c) => D::Conv(match c {
                crate::ast::Conv::Var(v) => match map.get(v) {
                    Some(D::Conv(by)) => *by,
                    _ => *c,
                },
                c => *c,
            }),
        }
    }

    /// The descriptions in `d` that are types, for analyses that look
    /// through what a value holds: a type itself, or, in a function, its
    /// body's types (its parameters standing for what it is given).
    pub(crate) fn d_types(&self, d: &D) -> Vec<TyId> {
        match d {
            D::Type(t) => vec![*t],
            D::Fun(f) => match self.arena.get(*f) {
                Ty::Lam { body, .. } => self.d_types(body),
                _ => Vec::new(),
            },
            _ => Vec::new(),
        }
    }

    /// The regions a description names outright: a region, an effect's
    /// atoms' regions, and a function's body's.
    pub(crate) fn d_regions(&self, d: &D) -> Vec<Region> {
        match d {
            D::Region(r) => vec![*r],
            D::Effect(e) => e.0.iter().filter_map(|a| a.region()).collect(),
            D::Fun(f) => match self.arena.get(*f) {
                Ty::Lam { body, .. } => self.d_regions(body),
                _ => Vec::new(),
            },
            _ => Vec::new(),
        }
    }

    /// The effects a description is or names: an effect, or a function's
    /// body's.
    pub(crate) fn d_effects(&self, d: &D) -> Vec<Effect> {
        match d {
            D::Effect(e) => vec![e.clone()],
            D::Fun(f) => match self.arena.get(*f) {
                Ty::Lam { body, .. } => self.d_effects(body),
                _ => Vec::new(),
            },
            _ => Vec::new(),
        }
    }

    /// Whether `d` mentions effect `e` writing region `r`, for `writes_in`.
    pub(crate) fn d_writes(&self, d: &D, r: Region) -> bool {
        match d {
            D::Region(x) => *x == r,
            D::Effect(e) => e.0.contains(&crate::ast::Atom::Write(r)),
            D::Fun(f) => match self.arena.get(*f) {
                Ty::Lam { body, .. } => self.d_writes(body, r),
                _ => false,
            },
            _ => false,
        }
    }

    /// The `which`th generative type as a description function of kind
    /// `want`, `(dlambda ((p k) …) (name p …))`; `None` if it is not of
    /// that kind.
    pub(crate) fn generative_fun(&mut self, which: u32, want: Kind) -> Option<TyId> {
        let params = self.generatives[which as usize].params.clone();
        let kinds: Vec<Kind> = params.iter().map(|(_, k)| *k).collect();
        if self.arena.arrow(kinds, Kind::Type) != want {
            return None;
        }
        let fresh: Vec<(DVar, Kind)> = params.iter().map(|(p, k)| (self.arena.dvar_of(self.arena.dvar_name(*p), *k), *k)).collect();
        let args: Vec<D> = fresh.iter().map(|(v, k)| self.var_d(*v, *k)).collect();
        let body = self.arena.ty(Ty::Named { which, args });
        Some(self.lam(fresh, D::Type(body)))
    }

    /// Variable `v`, of kind `k`, as a description.
    pub(crate) fn var_d(&mut self, v: DVar, k: Kind) -> D {
        match k {
            Kind::Region | Kind::Place => D::Region(Region::Var(v)),
            Kind::Effect => D::Effect(Effect::atom(crate::ast::Atom::Var(v))),
            Kind::Size => D::Size(Size::var(v)),
            Kind::Conv => D::Conv(crate::ast::Conv::Var(v)),
            Kind::Type | Kind::Data => D::Type(self.arena.ty(Ty::Var(v))),
            Kind::Arrow(_) => D::Fun(self.arena.ty(Ty::Var(v))),
        }
    }

    // ------------------------------------------------------------ reading

    /// A description function, as written where one of kind `want` (if
    /// known) is wanted: a name bound to one, a type family's or generative
    /// type's name, a type form's name (`listof`), `(dlambda ((x k) …) d)`
    /// or `(select m f)`.
    pub(crate) fn parse_fun(&mut self, s: &Syntax, want: Option<Kind>) -> R<TyId> {
        let f = self.parse_fun_node(s, want)?;
        if let Some(w) = want
            && let Some(got) = self.fun_kind(f)
            && got != w
        {
            return Err(FxError::at(
                s.span,
                format!("a description function of kind {} is wanted, and this is of kind {}", self.show_kind(w), self.show_kind(got)),
            ));
        }
        Ok(f)
    }

    fn parse_fun_node(&mut self, s: &Syntax, want: Option<Kind>) -> R<TyId> {
        if let Some(sym) = s.as_symbol() {
            let name = self.interner.name(sym).to_string();
            let params: Option<Vec<(Sym, Kind)>> = match self.lookup_desc(sym) {
                Some(DScope::Var(v, Kind::Arrow(_))) => return Ok(self.arena.ty(Ty::Var(v))),
                Some(DScope::Fun(f)) => return Ok(f),
                Some(DScope::Abbrev { params, .. }) if !params.is_empty() => Some(params),
                Some(DScope::Generative(g)) if !self.generatives[g as usize].params.is_empty() => {
                    let ps = self.generatives[g as usize].params.clone();
                    Some(ps.iter().map(|(v, k)| (self.arena.dvar_name(*v), *k)).collect())
                }
                None => CONSTRUCTORS
                    .iter()
                    .find(|(n, _)| *n == name)
                    .map(|(_, ps)| ps.iter().map(|(n, k)| (self.interner.intern(n), *k)).collect()),
                _ => None,
            };
            return match params {
                Some(ps) => self.fun_by_eta(s, &ps),
                None => Err(FxError::at(s.span, format!("`{name}` is not a description function"))),
            };
        }
        let usage = "a description function: a name, `(dlambda ((name kind) …) description)` or `(select module name)`";
        let items = s.as_proper_list().ok_or_else(|| FxError::at(s.span, usage))?.to_vec();
        let head = items.first().and_then(|h| h.as_symbol()).map(|h| self.interner.name(h).to_string());
        match head.as_deref() {
            Some("dlambda") => {
                let [_, binders, body] = &items[..] else {
                    return Err(FxError::at(s.span, "`(dlambda ((name kind) …) description)`"));
                };
                let result = want.and_then(|k| self.arena.arrow_parts(k).map(|(_, r)| r));
                let depth = self.dscope.len();
                let parsed = self.parse_binders(binders).and_then(|bs| {
                    if bs.is_empty() {
                        return Err(FxError::at(binders.span, "a `dlambda` takes at least one description"));
                    }
                    let body = match result {
                        Some(k) => self.parse_desc_at(body, k)?,
                        None => self.parse_d(body)?,
                    };
                    Ok((bs, body))
                });
                self.dscope.truncate(depth);
                let (bs, body) = parsed?;
                Ok(self.lam(bs, body))
            }
            // `(g d …)`, where `g` gives a description function.
            Some(h) if h != "select" && items[0].as_symbol().is_some_and(|x| self.fun_sym(x)) => {
                let g = self.parse_fun(&items[0], None)?;
                let shown = self.show_fun(g);
                let parts = self.fun_kind(g).and_then(|k| self.arena.arrow_parts(k).map(|(p, r)| (p.to_vec(), r)));
                let Some((params, Kind::Arrow(_))) = parts else {
                    return Err(FxError::at(s.span, format!("`{shown}` does not give a description function")));
                };
                if items.len() - 1 != params.len() {
                    return Err(FxError::at(s.span, format!("`{shown}` takes {} description(s), and has {}", params.len(), items.len() - 1)));
                }
                let mut ds = Vec::new();
                for (a, k) in items[1..].iter().zip(params) {
                    ds.push(self.parse_desc_at(a, k)?);
                }
                match self.apply_fun(g, ds) {
                    D::Fun(f) => Ok(f),
                    _ => Err(FxError::at(s.span, format!("`{shown}` does not give a description function"))),
                }
            }
            Some("select") => match &items[..] {
                [_, m, n] if m.as_symbol().is_some() && n.as_symbol().is_some() => {
                    Ok(self.arena.ty(Ty::Select(m.as_symbol().expect("a name"), n.as_symbol().expect("a name"))))
                }
                _ => Err(FxError::at(s.span, "`(select module name)`: a module's name, and a component's")),
            },
            _ => Err(FxError::at(s.span, usage)),
        }
    }

    /// The function a type family, generative type or type form `s` is:
    /// `(dlambda ((p k) …) (s p …))`.
    fn fun_by_eta(&mut self, s: &Syntax, params: &[(Sym, Kind)]) -> R<TyId> {
        let depth = self.dscope.len();
        let mut bound = Vec::new();
        let mut applied = vec![s.clone()];
        for (n, k) in params {
            let v = self.arena.dvar_of(*n, *k);
            self.dscope.push((*n, DScope::Var(v, *k)));
            bound.push((v, *k));
            applied.push(Syntax::symbol(s.span, *n));
        }
        let t = self.parse_type(&Syntax::list(s.span, applied));
        self.dscope.truncate(depth);
        Ok(self.lam(bound, D::Type(t?)))
    }

    /// A description of kind `k`, as written.
    pub(crate) fn parse_desc_at(&mut self, s: &Syntax, k: Kind) -> R<D> {
        Ok(match k {
            Kind::Type | Kind::Data => D::Type(self.parse_type(s)?),
            Kind::Region => D::Region(self.parse_region(s)?),
            Kind::Place => D::Region(self.parse_place(s)?),
            Kind::Effect => D::Effect(self.parse_effect(s)?),
            Kind::Size => D::Size(self.parse_size(s)?),
            Kind::Conv => D::Conv(self.parse_conv(s)?),
            Kind::Arrow(_) => D::Fun(self.parse_fun(s, Some(k))?),
        })
    }

    /// `(f d …)` as a type: `f` given the descriptions `args` are, of the
    /// kinds it takes; reduced, if it is a `dlambda`. Where `f`'s kind is
    /// not known yet (a `select`), what it is given is read by its shape,
    /// and checked once it is resolved.
    pub(crate) fn parse_app(&mut self, s: &Syntax, f: TyId, args: &[Syntax]) -> R<TyId> {
        let parts = self.fun_kind(f).and_then(|k| self.arena.arrow_parts(k).map(|(p, r)| (p.to_vec(), r)));
        let Some((params, result)) = parts else {
            let ds = args.iter().map(|a| self.parse_d(a)).collect::<R<Vec<_>>>()?;
            return Ok(self.arena.ty(Ty::App { fun: f, args: ds }));
        };
        let shown = self.show_fun(f);
        if args.len() != params.len() {
            return Err(FxError::at(s.span, format!("`{shown}` takes {} description(s), and has {}", params.len(), args.len())));
        }
        if !matches!(result, Kind::Type | Kind::Data) {
            return Err(FxError::at(s.span, format!("`{shown}` gives a description of kind {}, not a type", self.show_kind(result))));
        }
        let mut ds = Vec::new();
        for (a, k) in args.iter().zip(params) {
            ds.push(self.parse_desc_at(a, k)?);
        }
        match self.apply_fun(f, ds) {
            D::Type(t) => Ok(t),
            _ => Err(FxError::at(s.span, format!("`{shown}` does not give a type"))),
        }
    }

    /// Name `sym`, a description function, written where a type is wanted.
    pub(crate) fn not_applied(&self, s: &Syntax, sym: Sym, k: Kind) -> FxError {
        let n = self.interner.name(sym);
        FxError::at(s.span, format!("`{n}` is a description function, of kind {}: it is applied, `({n} …)`", self.show_kind(k)))
    }

    /// A description function as it is written: its name, or its `dlambda`.
    pub(crate) fn show_fun(&self, f: TyId) -> String {
        self.show_ty(f)
    }

    /// `(e d …)` in an effect, where `e` is a description function to an
    /// effect: its effect, reduced if it is a `dlambda`; `None` if `items`
    /// are not such an application.
    pub(crate) fn effect_app(&mut self, s: &Syntax, items: &[Syntax]) -> R<Option<Effect>> {
        let Some(head) = items.first() else { return Ok(None) };
        let f = match head.as_symbol() {
            Some(h) => match self.lookup_desc(h) {
                Some(DScope::Var(v, Kind::Arrow(_))) => self.arena.ty(Ty::Var(v)),
                Some(DScope::Fun(f)) => f,
                _ => return Ok(None),
            },
            None if head.as_proper_list().is_some_and(|l| l.first().and_then(|x| x.as_symbol()).is_some_and(|x| self.interner.name(x) == "dlambda")) => {
                self.parse_fun(head, None)?
            }
            None => return Ok(None),
        };
        let shown = self.show_fun(f);
        let parts = self.fun_kind(f).and_then(|k| self.arena.arrow_parts(k).map(|(p, r)| (p.to_vec(), r)));
        let Some((params, result)) = parts else { return Ok(None) };
        if result != Kind::Effect {
            return Err(FxError::at(s.span, format!("`{shown}` gives a description of kind {}, not an effect", self.show_kind(result))));
        }
        let args = &items[1..];
        if args.len() != params.len() {
            return Err(FxError::at(s.span, format!("`{shown}` takes {} description(s), and has {}", params.len(), args.len())));
        }
        let mut ds = Vec::new();
        for (a, k) in args.iter().zip(params) {
            ds.push(self.parse_desc_at(a, k)?);
        }
        match self.apply_fun(f, ds) {
            D::Effect(e) => Ok(Some(e)),
            _ => Err(FxError::at(s.span, format!("`{shown}` does not give an effect"))),
        }
    }

    /// Whether `sym` is bound to a description function.
    fn fun_sym(&self, sym: Sym) -> bool {
        matches!(self.lookup_desc(sym), Some(DScope::Var(_, Kind::Arrow(_)) | DScope::Fun(_)))
    }
}
