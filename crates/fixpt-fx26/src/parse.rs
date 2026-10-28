//! Syntax to the kernel.
//!
//! The forms are FX-87's (`docs/fx26.md`, "The kernel"): n-ary forms, binder
//! lists in parentheses — `(plambda ((t type)) …)` — and `@name` for a region
//! constant. The lexical syntax is FX-26's own, `SyntaxProfile::FX26`. `let` and `begin` are derived forms, and `lambda` and `letrec`
//! bodies are implicit `begin`s. A `lambda` parameter may be a bare name, when
//! the `lambda` is checked against a type that says what it is.

use crate::ast::{Arm, ArmBind, Atom, BlobletOp, Conv, D, DVar, Effect, Exp, ExpId, IoKind, Kind, ModItem, Region, RegionForm, Size, Ty, TyId, Variance};
use crate::check::Checker;
use crate::error::{FxError, R};
use fixpt_read::{Datum, Sym, Syntax};

/// A fixnum's range, as the heap's (`fixpt_heap::Value::try_fixnum`): an
/// integer literal past it is a bignum, made by arithmetic.
const FIXNUM_MAX: i64 = (1 << 60) - 1;
const FIXNUM_MIN: i64 = -(1 << 60);

/// What a description name means where it is used.
#[derive(Clone, Debug)]
pub enum DScope {
    Var(DVar, Kind),
    /// A name bound by `dletrec`: a type.
    Rec(TyId),
    /// A name bound by `define-type` with parameters: a type abbreviation
    /// with holes, expanded at each use by parsing its body with the
    /// parameters bound to the descriptions given.
    Abbrev { params: Vec<(Sym, Kind)>, body: Syntax },
    /// A region given for an abbreviation's region parameter.
    Region(Region),
    /// A size given for an abbreviation's size parameter.
    SizeVal(Size),
    /// A convention given for an abbreviation's convention parameter.
    ConvVal(Conv),
    /// A name bound by `define-effect`: an effect.
    Eff(crate::ast::Effect),
    /// A name bound by `define-generative`: the `n`th generative type.
    Generative(u32),
    /// A name for a description function: `define-type` of a `dlambda`,
    /// or a type family's parameter of an arrow kind given one.
    Fun(TyId),
    /// A `(with m …)` body's start, under the name `%with`: a type name
    /// bound before it is `m`'s, if `m` gives it (`with_selected`).
    With(Sym),
}

/// A description given a type family, as a key for its knot.
#[derive(Clone, PartialEq, Debug)]
pub enum FamilyArg {
    Ty(TyId),
    Region(Region),
    Eff(crate::ast::Effect),
    Size(Size),
    Conv(Conv),
    Fun(TyId),
}

/// The heads of the type forms `parse_type_node` reads.
/// What `(abs (f (name kind) …) type)` is, when it is not.
const ABS_CTOR_USAGE: &str = "an abstract type constructor is `(abs (f (name kind) …) type)`";

/// Where `->*` is not a definition's signature.
const ARROW_STAR_ONLY: &str = "`(->* (param …) result)` is only the type a definition declares (`define`, `define-rec`, `letrec`), \
     its effect found from its `lambda`: here, write `->` or `subr`";

const TYPE_FORMS: &[&str] = &[
    "arrayof", "narrayof", "bloblet", "composable", "dletrec", "icell", "listof", "mark-key", "moduleof", "mu", "nat", "nlist", "oneshot", "pairof", "place",
    "poly", "productof", "prompt-tag", "proves", "ref", "select", "subr", "sumof", "bool", "union", "->", "->*", "restrict",
];

impl Checker {
    pub(crate) fn name(&self, s: Sym) -> &str {
        self.interner.name(s)
    }

    /// The region `@name` stands for: the constant of that name.
    pub(crate) fn region_constant(&self, sym: Sym) -> Region {
        Region::Const(sym)
    }

    /// The modules of the `with`s whose bodies `s` is read in since it was
    /// last bound, innermost first: each shadows what `s` was before it.
    fn withs_over(&self, s: Sym) -> Vec<Sym> {
        let hidden = self.hidden.map(|(_, d)| d);
        let mut out = Vec::new();
        if self.with_depth == 0 {
            return out;
        }
        for i in (0..self.dscope.len()).rev() {
            if hidden.is_some_and(|(a, b)| (a..b).contains(&i)) {
                continue;
            }
            match &self.dscope[i] {
                (n, _) if *n == s => break,
                (_, DScope::With(m)) => out.push(*m),
                _ => {}
            }
        }
        out
    }

    /// Type name `sym`, read in the bodies of `with`s of modules `withs`
    /// (innermost first): `(select m sym)` of the innermost, which, where
    /// `m` does not give it, is the next's, and so on out to what `sym`
    /// means here otherwise, `outer` (FX-91 §2.3.19: `with` shadows).
    fn with_selected(&mut self, withs: &[Sym], sym: Sym, outer: Option<TyId>) -> TyId {
        let mut t = outer;
        for m in withs.iter().rev() {
            let node = self.arena.ty(Ty::Select(*m, sym));
            self.arena.with_fallback.insert(node, t);
            t = Some(node);
        }
        t.expect("a `with`")
    }

    /// `(f d …)`, `s`, read in the bodies of `with`s of modules `withs`
    /// (innermost first): `((select m f) d …)` of the innermost, which,
    /// where `m` does not give `f`, is the next's, and so on out to what
    /// `s` means here otherwise, `outer`; as `with_selected` for a name.
    fn with_applied(&mut self, s: &Syntax, withs: &[Sym], f: Sym, outer: Option<TyId>) -> R<TyId> {
        let args = &self.items(s, "a type")?.to_vec()[1..];
        let mut t = outer;
        for m in withs.iter().rev() {
            let fun = self.arena.ty(Ty::Select(*m, f));
            let ds = args.iter().map(|a| self.parse_d(a)).collect::<R<Vec<_>>>()?;
            let app = self.arena.ty(Ty::App { fun, args: ds });
            self.arena.with_fallback.insert(fun, t);
            self.arena.with_applied.insert(fun, app);
            t = Some(app);
        }
        Ok(t.expect("a `with`"))
    }

    /// What `read` reads, in the body of a `(with m …)`: `m`'s type names
    /// shadowing those before (`withs_over`); `#%fx`'s are the standard's.
    fn with_types_of<T>(&mut self, m: Sym, read: impl FnOnce(&mut Self) -> R<T>) -> R<T> {
        if self.name(m) == "#%fx" {
            return read(self);
        }
        let depth = self.dscope.len();
        let mark = self.interner.intern("%with");
        self.dscope.push((mark, DScope::With(m)));
        self.with_depth += 1;
        let r = read(self);
        self.with_depth -= 1;
        self.dscope.truncate(depth);
        r
    }

    pub(crate) fn lookup_desc(&self, s: Sym) -> Option<DScope> {
        let hidden = self.hidden.map(|(_, d)| d);
        (0..self.dscope.len())
            .rev()
            .find(|i| self.dscope[*i].0 == s && !hidden.is_some_and(|(a, b)| (a..b).contains(i)))
            .map(|i| self.dscope[i].1.clone())
    }

    fn items<'s>(&self, s: &'s Syntax, what: &str) -> R<&'s [Syntax]> {
        s.as_proper_list().ok_or_else(|| FxError::at(s.span, format!("{what}: expected a list")))
    }

    fn literal_int(&self, s: &Syntax) -> Option<i64> {
        match &s.datum {
            Datum::Number(fixpt_read::Num::Int(n)) => Some(*n),
            _ => None,
        }
    }

    pub(crate) fn head(&self, items: &[Syntax]) -> Option<&str> {
        items.first().and_then(|h| h.as_symbol()).map(|h| self.name(h))
    }

    // --------------------------------------------------------------- kinds
    pub(crate) fn parse_kind(&mut self, s: &Syntax) -> R<Kind> {
        let usage = "a kind is `region`, `place`, `effect`, `type`, `data`, `sendable`, `flat`, `size`, `conv` or `(=> (kind …) kind)`";
        // `(=> (k1 … kn) k)`: a description function's (`crate::kinds`).
        if let Some([head, ks, result]) = s.as_proper_list()
            && head.as_symbol().is_some_and(|h| self.name(h) == "=>")
            && let Some(ks) = ks.as_proper_list()
            && !ks.is_empty()
        {
            let params = ks.iter().map(|k| self.parse_kind(k)).collect::<R<Vec<_>>>()?;
            let at = result.span;
            let result = self.parse_kind(result)?;
            if matches!(result, Kind::Region | Kind::Place | Kind::Size | Kind::Conv) {
                return Err(FxError::at(at, "a description function gives a type, an effect, or another description function"));
            }
            if result == Kind::Effect && params.iter().any(|k| matches!(k, Kind::Type | Kind::Data | Kind::Sendable | Kind::Flat | Kind::Arrow(_))) {
                return Err(FxError::at(s.span, "a description function to an effect takes regions, places, effects, sizes and conventions"));
            }
            return Ok(self.arena.arrow(params, result));
        }
        match s.as_symbol().map(|k| self.name(k)) {
            Some("region") => Ok(Kind::Region),
            Some("place") => Ok(Kind::Place),
            Some("effect") => Ok(Kind::Effect),
            Some("type") => Ok(Kind::Type),
            Some("data") => Ok(Kind::Data),
            Some("sendable") => Ok(Kind::Sendable),
            Some("flat") => Ok(Kind::Flat),
            Some("size") => Ok(Kind::Size),
            Some("conv") => Ok(Kind::Conv),
            _ => Err(FxError::at(s.span, usage)),
        }
    }

    /// `(conv C)`: the convention `C`.
    fn parse_conv_form(&self, s: &Syntax) -> R<Conv> {
        match self.items(s, "`(conv convention)`")? {
            [_, c] => self.parse_conv(c),
            _ => Err(FxError::at(s.span, "`(conv convention)`")),
        }
    }

    /// A convention: `cellular`, `native`, `fx`, or a name bound as one.
    pub(crate) fn parse_conv(&self, s: &Syntax) -> R<Conv> {
        let Some(sym) = s.as_symbol() else {
            return Err(FxError::at(s.span, "a convention is `cellular`, `native`, `fx`, or a name bound as one"));
        };
        match self.name(sym) {
            "cellular" => Ok(Conv::Cellular),
            "native" => Ok(Conv::Native),
            "fx" => Ok(Conv::Fx),
            _ => match self.lookup_desc(sym) {
                Some(DScope::Var(v, Kind::Conv)) => Ok(Conv::Var(v)),
                Some(DScope::ConvVal(c)) => Ok(c),
                _ => Err(FxError::at(s.span, format!("`{}` is not a convention", self.name(sym)))),
            },
        }
    }

    /// `((I K) …)`, binding each name for the rest of the parse.
    pub(crate) fn parse_binders(&mut self, s: &Syntax) -> R<Vec<(DVar, Kind)>> {
        let mut out = Vec::new();
        for b in self.items(s, "binders")? {
            let pair = self.items(b, "a binder")?;
            // A region binder marked `distinct`, last: one that aliases no
            // other region its procedure sees (`docs/research/
            // region-anti-aliasing.md`, (C)).
            let (pair, distinct) = match pair.split_last() {
                Some((last, rest)) if rest.len() >= 2 && last.as_symbol().is_some_and(|x| self.name(x) == "distinct") => (rest, true),
                _ => (pair, false),
            };
            let (name, kind, bound) = match pair {
                [name, kind] => (name, kind, None),
                [name, kind, bound] => (name, kind, Some(bound)),
                _ => return Err(FxError::at(b.span, "a binder is `(name kind)`, `(name region place)` or `(name data place)`, a region's perhaps `distinct` last")),
            };
            let name = name.as_symbol().ok_or_else(|| FxError::at(name.span, "a binder's name"))?;
            let kind = self.parse_kind(kind)?;
            // `(r region p)`: a region that won't outlive `p`, a place
            // bound before it. `(t data p)`: data at `p` or the heap
            // (`docs/research/shapes.md`; F13).
            let bound = match bound {
                Some(p) if matches!(kind, Kind::Region | Kind::Data) => Some(self.parse_place(p)?),
                Some(p) => {
                    return Err(FxError::at(p.span, "only a region or data binder has a bound: `(name region place)` or `(name data place)`"));
                }
                None => None,
            };
            if distinct && kind != Kind::Region {
                return Err(FxError::at(b.span, "only a region binder is `distinct`"));
            }
            let v = self.arena.dvar_of(name, kind);
            if let Some(p) = bound {
                self.arena.set_bound(v, p);
            }
            if distinct {
                self.arena.set_distinct(v);
            }
            self.dscope.push((name, DScope::Var(v, kind)));
            out.push((v, kind));
        }
        Ok(out)
    }

    // ------------------------------------------------------------- regions
    /// `@globals`, or `(globals g …)` as the regions of each `g`; `None` if
    /// `s` is neither.
    fn globals_region(&self, s: &Syntax) -> R<Option<Vec<Region>>> {
        if s.as_symbol().is_some_and(|x| self.name(x) == "@globals") {
            return Ok(Some(vec![Region::Globals]));
        }
        let Some([head, names @ ..]) = s.as_proper_list() else { return Ok(None) };
        if !head.as_symbol().is_some_and(|h| self.name(h) == "globals") {
            return Ok(None);
        }
        if names.is_empty() {
            return Err(FxError::at(s.span, "`(globals name …)`: at least one global"));
        }
        names.iter().map(|n| n.as_symbol().map(Region::Global).ok_or_else(|| FxError::at(n.span, "a global's name"))).collect::<R<_>>().map(Some)
    }

    pub(crate) fn parse_region(&self, s: &Syntax) -> R<Region> {
        if self.globals_region(s)?.is_some() {
            return Err(FxError::at(s.span, "globals are a region only in effects: `(read @globals)`, `(write (globals g))`"));
        }
        // `(const p)`: data frozen into place `p`; `(acyclic p)`, and never
        // written, so with no cycle through it.
        if let Some([head, p]) = s.as_proper_list()
            && let Some(h) = head.as_symbol()
            && matches!(self.name(h), "const" | "acyclic")
        {
            let acyclic = self.name(h) == "acyclic";
            return Ok(match self.parse_place(p)? {
                Region::Var(v) => Region::Frozen(Some(v), acyclic),
                _ => Region::Frozen(None, acyclic),
            });
        }
        let Some(sym) = s.as_symbol() else {
            return Err(FxError::at(s.span, "expected a region"));
        };
        if self.name(sym).starts_with('@') {
            return Ok(self.region_constant(sym));
        }
        match self.name(sym) {
            "const" => return Ok(Region::Frozen(None, false)),
            "acyclic" => return Ok(Region::Frozen(None, true)),
            "finite" => return Err(FxError::at(s.span, "`finite` is a size; data with no cycle through it is at `acyclic`")),
            "heap" => return Ok(Region::Heap),
            _ => {}
        }
        match self.lookup_desc(sym) {
            Some(DScope::Var(v, Kind::Region | Kind::Place)) => Ok(Region::Var(v)),
            Some(DScope::Region(r)) => Ok(r),
            _ => Err(FxError::at(s.span, format!("`{}` is not a region", self.name(sym)))),
        }
    }

    /// A place: a region that is one.
    pub(crate) fn parse_place(&self, s: &Syntax) -> R<Region> {
        let r = self.parse_region(s)?;
        if !self.arena.is_place(r) {
            return Err(FxError::at(s.span, format!("`{}` is not a place", self.show_region(r))));
        }
        Ok(r)
    }

    /// `(subr effect (param …) result)`, or with a convention first,
    /// `(subr (conv C) effect (param …) result)`; left out, it is the
    /// program's (`docs/research/native-conventions.md`). Or `(-> (param …)
    /// result)`: `(subr pure (param …) result)`. `clauses`, its
    /// specification's, if it has one.
    fn parse_subr_form(&mut self, s: &Syntax, items: &[Syntax], clauses: &[Syntax]) -> R<TyId> {
        if self.head(items) == Some("->") {
            let [_, params, result] = items else {
                return Err(FxError::at(s.span, "`(-> (param …) result)`"));
            };
            return self.parse_subr_type(self.conv_default, Effect::pure(), params, result, clauses);
        }
        let (conv, rest) = match items {
            [_, c, rest @ ..] if rest.len() == 3 && self.head(&self.items(c, "a convention").unwrap_or_default()) == Some("conv") => {
                (self.parse_conv_form(c)?, rest)
            }
            [_, rest @ ..] => (self.conv_default, rest),
            [] => unreachable!("a head"),
        };
        let [effect, params, result] = rest else {
            return Err(FxError::at(s.span, "`(subr effect (param …) result)`"));
        };
        let effect = self.parse_effect(effect)?;
        self.parse_subr_type(conv, effect, params, result, clauses)
    }

    /// A procedure type's parameters and result, after its convention and
    /// effect: `(subr …)`'s and `(-> …)`'s.
    fn parse_subr_type(&mut self, conv: Conv, effect: Effect, params: &Syntax, result: &Syntax, clauses: &[Syntax]) -> R<TyId> {
        let ps = match &params.datum {
            Datum::Nil => Vec::new(),
            _ => self.items(params, "parameter types")?.to_vec(),
        };
        // A parameter may be named, `(name : type)`, for the types after
        // it to select from (a dependent procedure, M5), and for a
        // specification's clauses.
        let mut names: Vec<Option<Sym>> = Vec::new();
        let mut params = Vec::new();
        for (i, p) in ps.iter().enumerate() {
            let later: Vec<&Syntax> = ps[i + 1..].iter().chain([result]).chain(clauses).collect();
            self.misnamed_param(p, &later)?;
            let (name, t) = match self.named_param(p) {
                Some((n, t)) => (Some(n), t),
                None => (None, p.clone()),
            };
            let t = self.parse_type(&t)?;
            params.push(self.select_params(t, &names));
            names.push(name);
        }
        // A test's result, `(bool …)`: here, and only here, a `bool` and
        // what it proves, an `ensures` of it.
        let (result, spec) = match result.as_proper_list().and_then(|l| l.first()).and_then(|h| h.as_symbol()) {
            Some(h) if self.name(h) == "bool" => {
                let ensures = self.parse_proving(result, params.len())?;
                let spec = crate::ast::Spec { params: names.clone(), result: None, requires: crate::logic::Formula::True, ensures };
                (self.bool_, Some(std::rc::Rc::new(spec)))
            }
            _ => (self.parse_type(result)?, None),
        };
        let result = self.select_params(result, &names);
        Ok(self.arena.ty(Ty::Subr { conv, effect, params, result, spec }))
    }

    // ------------------------------------------------------------- effects
    pub(crate) fn parse_effect(&mut self, s: &Syntax) -> R<Effect> {
        if let Some(sym) = s.as_symbol() {
            if self.name(sym) == "pure" {
                return Ok(Effect::pure());
            }
            if self.name(sym) == "spin" {
                return Ok(Effect::atom(Atom::Spin));
            }
            if self.name(sym) == "nondet" {
                return Ok(Effect::atom(Atom::Nondet));
            }
            let withs = self.withs_over(sym);
            if !withs.is_empty() {
                let outer = if self.lookup_desc(sym).is_some() || self.include_scope > 0 { Some(self.effect_name_read(s, sym)?) } else { None };
                return Ok(self.with_effect_selected(&withs, sym, outer));
            }
            return self.effect_name_read(s, sym);
        }
        self.parse_effect_list(s)
    }

    /// Effect name `sym`, as `with_selected` makes a type name: an effect
    /// variable for `(select m sym)` of each `with`'s module `m`, not shared
    /// (`effect_select`'s are), each falling back to the next, out to `outer`.
    fn with_effect_selected(&mut self, withs: &[Sym], sym: Sym, outer: Option<Effect>) -> Effect {
        let mut e = outer;
        for m in withs.iter().rev() {
            let shown = format!("(select {} {})", self.name(*m), self.name(sym));
            let v = self.arena.dvar_of(self.interner.intern(&shown), Kind::Effect);
            self.effect_selects.push(((*m, sym), v));
            self.with_effect_fallback.insert(v, e);
            e = Some(Effect::atom(Atom::Var(v)));
        }
        e.expect("a `with`")
    }

    /// Effect name `sym`, as the description scope and `include`s say.
    fn effect_name_read(&mut self, s: &Syntax, sym: Sym) -> R<Effect> {
        match self.lookup_desc(sym) {
            Some(DScope::Var(v, Kind::Effect)) => Ok(Effect::atom(Atom::Var(v))),
            Some(DScope::Eff(e)) => Ok(e),
            // In a module with `include`s, the modules included's, as a
            // type's (`include_scope`).
            _ if self.include_scope > 0 => {
                let inc = self.interner.intern("%include");
                Ok(Effect::atom(Atom::Var(self.effect_select(inc, sym))))
            }
            _ => Err(FxError::at(s.span, format!("`{}` is not an effect", self.name(sym)))),
        }
    }

    fn parse_effect_list(&mut self, s: &Syntax) -> R<Effect> {
        let items = self.items(s, "an effect")?.to_vec();
        // `(select m e)`: module `m`'s effect `e`, found where the type it
        // is in is checked, as a type's `select` is (`resolve_selects`).
        if self.head(&items) == Some("select") {
            let [_, m, e] = &items[..] else {
                return Err(FxError::at(s.span, "`(select module name)`: a module's name, and a component's"));
            };
            let (Some(m), Some(e)) = (m.as_symbol(), e.as_symbol()) else {
                return Err(FxError::at(s.span, "`(select module name)`: a module's name, and a component's"));
            };
            return Ok(Effect::atom(Atom::Var(self.effect_select(m, e))));
        }
        // `(e d …)`: a description function to an effect, applied.
        if let Some(e) = self.effect_app(s, &items)? {
            return Ok(e);
        }
        let items = &items[..];
        let head = self.head(items).unwrap_or("");
        let atom = |c: fn(Region) -> Atom| -> R<Effect> {
            let [_, r] = items else {
                return Err(FxError::at(s.span, format!("`({head} region)`")));
            };
            // Globals' bindings, which are only read and written.
            if let Some(gs) = self.globals_region(r)? {
                if !matches!(head, "read" | "write") {
                    return Err(FxError::at(r.span, format!("globals are only read and written, not `{head}`")));
                }
                return Ok(Effect(gs.into_iter().map(c).collect()));
            }
            Ok(Effect::atom(c(self.parse_region(r)?)))
        };
        match head {
            "read" => atom(Atom::Read),
            "write" => atom(Atom::Write),
            "alloc" => atom(Atom::Alloc),
            "goto" => atom(Atom::Goto),
            "comefrom" => atom(Atom::Comefrom),
            "await" => atom(Atom::Await),
            "init" => atom(Atom::Init),
            "send" => atom(Atom::Send),
            "receive" => atom(Atom::Receive),
            // `(io k)`, `k` one of the fixed family (`TODO.md` §84).
            "io" => {
                let kinds = || IoKind::ALL.map(|k| format!("`{}`", k.name())).join(", ");
                let [_, k] = items else {
                    return Err(FxError::at(s.span, format!("`(io kind)`, the kind one of {}", kinds())));
                };
                match k.as_symbol().and_then(|k| IoKind::named(self.name(k))) {
                    Some(k) => Ok(Effect::atom(Atom::Io(k))),
                    None => Err(FxError::at(k.span, format!("an I/O effect's kind is one of {}", kinds()))),
                }
            }
            "maxeff" => {
                let mut e = Effect::pure();
                for part in &items[1..] {
                    e = e.union(&self.parse_effect(part)?);
                }
                Ok(e)
            }
            _ => Err(FxError::at(s.span, "expected an effect")),
        }
    }

    // --------------------------------------------------------------- types
    pub fn parse_type(&mut self, s: &Syntax) -> R<TyId> {
        let t = match std::mem::take(&mut self.arrow_star) {
            true => {
                let t = self.parse_arrow_star(s)?;
                self.arrow_star_tys.insert(t);
                t
            }
            false => self.parse_type_node(s)?,
        };
        // Storage written: a procedure kept there may not reach itself
        // unsaid (`spin`).
        if matches!(self.head(self.items(s, "a type").unwrap_or(&[])), Some("ref" | "icell" | "pairof" | "listof" | "union" | "bloblet" | "arrayof" | "mark-key" | "mu")) {
            self.no_knot(t, s.span)?;
        }
        Ok(t)
    }

    /// Whether signature `s` is `(->* …)`, under any `poly`s.
    pub(crate) fn written_arrow_star(&self, s: &Syntax) -> bool {
        let items = s.as_proper_list().unwrap_or(&[]);
        match (self.head(items), items) {
            (Some("->*"), _) => true,
            (Some("poly"), [_, _, body]) => self.written_arrow_star(body),
            _ => false,
        }
    }

    /// A definition's signature that may be `(->* (param …) result)`, under
    /// any `poly`s: read as `(subr pure (param …) result)`, the effect the
    /// definition then finds standing in for its own (`top.rs`).
    fn parse_arrow_star(&mut self, s: &Syntax) -> R<TyId> {
        let items = self.items(s, "a type")?.to_vec();
        match (self.head(&items), &items[..]) {
            (Some("->*"), [_, params, result]) => self.parse_subr_type(self.conv_default, Effect::pure(), params, result, &[]),
            (Some("->*"), _) => Err(FxError::at(s.span, "`(->* (param …) result)`")),
            (Some("poly"), _) => {
                self.arrow_star = true;
                let t = self.parse_type_node(s);
                self.arrow_star = false;
                t
            }
            _ => self.parse_type_node(s),
        }
    }

    fn parse_type_node(&mut self, s: &Syntax) -> R<TyId> {
        if let Some(sym) = s.as_symbol() {
            let name = self.name(sym);
            if name == "void" {
                return Ok(self.void);
            }
            // The empty list's own type (`docs/research/logical-types.md`, L1).
            if name == "nil" && self.lookup_desc(sym).is_none() {
                return Ok(self.arena.ty(Ty::Nil));
            }
            // `#f`'s own type, below `bool` (L1's stage 3).
            if name == "false" && self.lookup_desc(sym).is_none() {
                return Ok(self.arena.ty(Ty::False));
            }
            if name == "nat" && self.lookup_desc(sym).is_none() {
                return Ok(self.arena.ty(Ty::Nat(Size::Finite)));
            }
            // A standard type, unless the program defines the name itself
            // (`TODO.md` §88), as it may `nil` and the rest above.
            if let Some(&t) = self.base.get(&sym)
                && self.lookup_desc(sym).is_none()
            {
                return Ok(t);
            }
            let withs = self.withs_over(sym);
            if !withs.is_empty() {
                let outer = if self.lookup_desc(sym).is_some() || self.include_scope > 0 { Some(self.type_name_read(s, sym)?) } else { None };
                return Ok(self.with_selected(&withs, sym, outer));
            }
            return self.type_name_read(s, sym);
        }
        // `(f d …)` in `with` bodies: the modules' `f` first, as names alone.
        let head = s.as_proper_list().and_then(|l| l.first()).and_then(|h| h.as_symbol());
        if let Some(head) = head.filter(|h| !TYPE_FORMS.contains(&self.name(*h))) {
            let withs = self.withs_over(head);
            if !withs.is_empty() {
                let outer = if self.lookup_desc(head).is_some() { Some(self.parse_type_list(s)?) } else { None };
                return self.with_applied(s, &withs, head, outer);
            }
        }
        self.parse_type_list(s)
    }

    /// Type name `sym`, as the description scope and `include`s say.
    fn type_name_read(&mut self, s: &Syntax, sym: Sym) -> R<TyId> {
        match self.lookup_desc(sym) {
            Some(DScope::Var(v, Kind::Type | Kind::Data | Kind::Sendable)) => Ok(self.arena.ty(Ty::Var(v))),
            // A flat is no type: it is reached through a `blobref`.
            Some(DScope::Var(_, Kind::Flat)) => Err(FxError::at(s.span, format!("`{}` is a flat, not a type", self.name(sym)))),
            // A family's flat parameter, a variable of kind `flat`, is no
            // type either.
            Some(DScope::Rec(t)) if matches!(self.arena.get(self.arena.resolve(t)), Ty::Var(v) if self.arena.dvar_kind_known(*v) == Some(Kind::Flat)) => {
                Err(FxError::at(s.span, format!("`{}` is a flat, not a type", self.name(sym))))
            }
            Some(DScope::Rec(t)) => Ok(t),
            Some(DScope::Generative(g)) => self.apply_generative(s, g, &[]),
            Some(DScope::Var(_, k @ Kind::Arrow(_))) => Err(self.not_applied(s, sym, k)),
            Some(DScope::Fun(f)) => {
                let k = self.fun_kind(f).unwrap_or(Kind::Type);
                Err(self.not_applied(s, sym, k))
            }
            _ if self.holes.is_some_and(|h| h.exp == sym) => Err(FxError::at(s.span, "expected a type")),
            // In a module with `include`s, the modules included's, found
            // when they are typed (`TODO.md` §69).
            _ if self.include_scope > 0 => {
                let inc = self.interner.intern("%include");
                Ok(self.arena.ty(Ty::Select(inc, sym)))
            }
            _ => Err(FxError::at(s.span, format!("`{}` is not a type", self.name(sym)))),
        }
    }

    fn parse_type_list(&mut self, s: &Syntax) -> R<TyId> {
        let items = self.items(s, "a type")?.to_vec();
        if let Some(head) = items.first().and_then(|h| h.as_symbol()) {
            match self.lookup_desc(head) {
                Some(DScope::Abbrev { params, body }) => return self.expand_abbrev(s, head, &params, &body, &items[1..]),
                Some(DScope::Generative(g)) => return self.apply_generative(s, g, &items[1..]),
                Some(DScope::Var(v, Kind::Arrow(_))) => {
                    let f = self.arena.ty(Ty::Var(v));
                    return self.parse_app(s, f, &items[1..]);
                }
                Some(DScope::Fun(f)) => return self.parse_app(s, f, &items[1..]),
                // A name for a module's family, `(define-type f (select m
                // f))`, applied: as `((select m f) d …)` (`TODO.md` §34).
                Some(DScope::Rec(t)) if matches!(self.arena.get(self.arena.resolve(t)), Ty::Select(..)) => {
                    let f = self.arena.resolve(t);
                    return self.parse_app(s, f, &items[1..]);
                }
                _ => {}
            }
        }
        // `((dlambda …) d …)` and `((select m f) d …)`: a function applied.
        if let Some(head) = items.first()
            && head.as_proper_list().is_some()
        {
            let f = self.parse_fun(head, None)?;
            return self.parse_app(s, f, &items[1..]);
        }
        match self.head(&items).unwrap_or("") {
            // `(subr effect (param …) result)`, or with a convention first,
            // `(subr (conv C) effect (param …) result)`; left out, it is the
            // program's (`docs/research/native-conventions.md`).
            "subr" | "->" if items.len() > 3 && crate::specs::clause(self, items.last().expect("items")) => {
                // A specification after the result: the type without it,
                // then the clauses read against its parameters.
                let n = items.iter().rev().take_while(|c| crate::specs::clause(self, c)).count();
                let (plain, clauses) = items.split_at(items.len() - n);
                // (The parameters are second to last, in either form.)
                let params = plain[plain.len() - 2].clone();
                let whole = Syntax { datum: Datum::List { items: plain.to_vec(), tail: None }, span: s.span };
                let t = self.parse_subr_form(&whole, plain, clauses)?;
                self.specified(t, &params, clauses)
            }
            "subr" | "->" => self.parse_subr_form(s, &items, &[]),
            "->*" => Err(FxError::at(s.span, ARROW_STAR_ONLY)),
            "bool" => Err(FxError::at(s.span, "`(bool …)` is a procedure's result, and only that")),
            // `(proves (<= A B))`, or `(proves (poly (binder …) (<= A B)
            // (<= X Y) …))`: the type of a proof that `A ≤ B` (given each
            // `X ≤ Y`), a function from a coercion for each hypothesis and
            // an `A` to a `B`, which may run for ever. The lemma waits for
            // the definition it declares (`crate::lemma`).
            "proves" => {
                let usage = "`(proves (<= type type))` or `(proves (poly ((name kind) …) (<= type type) (<= type type) …))`";
                let [_, prop] = &items[..] else {
                    return Err(FxError::at(s.span, usage));
                };
                let depth = self.dscope.len();
                let r = self.parse_proves(prop, usage);
                self.dscope.truncate(depth);
                r
            }
            "poly" => {
                let [_, binders, body] = &items[..] else {
                    return Err(FxError::at(s.span, "`(poly ((name kind) …) type)`"));
                };
                let depth = self.dscope.len();
                let binders = self.parse_binders(binders);
                let body = binders.and_then(|b| Ok((b, self.parse_type(body)?)));
                self.dscope.truncate(depth);
                let (binders, body) = body?;
                Ok(self.arena.ty(Ty::Poly { binders, body }))
            }
            // `(nlist T size)` or `(nlist T size p)`: a list frozen in the heap,
            // or into place `p`, with `size` elements.
            "nlist" => {
                let (t, size, place) = match &items[..] {
                    [_, t, n] => (t, n, None),
                    [_, t, n, p] => (t, n, Some(p)),
                    _ => return Err(FxError::at(s.span, "`(nlist type size)` or `(nlist type size place)`")),
                };
                let elem = self.parse_type(t)?;
                let size = self.parse_size(size)?;
                let region = match place {
                    None => Region::Frozen(None, true),
                    Some(p) => match self.parse_place(p)? {
                        Region::Var(v) => Region::Frozen(Some(v), true),
                        _ => Region::Frozen(None, true),
                    },
                };
                Ok(self.arena.ty(Ty::NList { elem, size, region }))
            }
            // `(nat size)`: exactly that natural.
            "nat" => {
                let [_, n] = &items[..] else {
                    return Err(FxError::at(s.span, "`(nat size)`"));
                };
                let size = self.parse_size(n)?;
                Ok(self.arena.ty(Ty::Nat(size)))
            }
            "ref" => {
                let [_, t, r] = &items[..] else {
                    return Err(FxError::at(s.span, "`(ref type region)`"));
                };
                let t = self.parse_type(t)?;
                let r = self.parse_region(r)?;
                Ok(self.arena.ty(Ty::Ref(t, r)))
            }
            "icell" => {
                let [_, t, r] = &items[..] else {
                    return Err(FxError::at(s.span, "`(icell type region)`"));
                };
                let t = self.parse_type(t)?;
                let r = self.parse_region(r)?;
                Ok(self.arena.ty(Ty::ICell(t, r)))
            }
            "place" => {
                let [_, r] = &items[..] else {
                    return Err(FxError::at(s.span, "`(place region)`"));
                };
                let r = self.parse_place(r)?;
                Ok(self.arena.ty(Ty::Place(r)))
            }
            "pairof" => {
                let [_, a, b, r] = &items[..] else {
                    return Err(FxError::at(s.span, "`(pairof type type region)`"));
                };
                let a = self.parse_type(a)?;
                let b = self.parse_type(b)?;
                let r = self.parse_region(r)?;
                Ok(self.arena.ty(Ty::Pair(a, b, r, false)))
            }
            // A union of members of disjoint shapes at run time
            // (`docs/research/logical-types.md`, L1), normalized.
            "union" => {
                if items.len() < 3 {
                    return Err(FxError::at(s.span, "`(union type type …)`"));
                }
                let mut members = Vec::new();
                for m in &items[1..] {
                    members.push(self.parse_type(m)?);
                }
                self.union_of(&members, s.span)
            }
            "dletrec" => self.parse_dletrec(s, &items),
            // `(mu name type)`: a recursive type, anonymous; the same as
            // `(dletrec ((name type)) name)`.
            "mu" => {
                let [_, name, body] = &items[..] else {
                    return Err(FxError::at(s.span, "`(mu name type)`"));
                };
                let name = name.as_symbol().ok_or_else(|| FxError::at(name.span, "a name"))?;
                let depth = self.dscope.len();
                let slot = self.arena.ty(Ty::Link(None));
                self.dscope.push((name, DScope::Rec(slot)));
                let t = self.parse_type(body);
                self.dscope.truncate(depth);
                self.arena.set_link(slot, t?);
                self.grounded(slot, s.span)?;
                Ok(slot)
            }
            "listof" => {
                // FX-87's `listof`: a pair whose tail is the list itself, or
                // the empty list, `nil`.
                let [_, t, r] = &items[..] else {
                    return Err(FxError::at(s.span, "`(listof type region)`"));
                };
                let t = self.parse_type(t)?;
                let r = self.parse_region(r)?;
                let slot = self.arena.ty(Ty::Link(None));
                let pair = self.arena.ty(Ty::Pair(t, slot, r, true));
                self.arena.set_link(slot, pair);
                Ok(slot)
            }
            "prompt-tag" => {
                let [_, a, h, d, r] = &items[..] else {
                    return Err(FxError::at(s.span, "`(prompt-tag answer payload effect region)`"));
                };
                let answer = self.parse_type(a)?;
                let payload = self.parse_type(h)?;
                let effect = self.parse_effect(d)?;
                let region = self.parse_region(r)?;
                Ok(self.arena.ty(Ty::PromptTag { answer, payload, effect, region }))
            }
            "composable" | "oneshot" => {
                let once = self.head(&items) == Some("oneshot");
                let [_, t, a, d, r] = &items[..] else {
                    let head = if once { "oneshot" } else { "composable" };
                    return Err(FxError::at(s.span, format!("`({head} argument answer effect region)`")));
                };
                let arg = self.parse_type(t)?;
                let answer = self.parse_type(a)?;
                let effect = self.parse_effect(d)?;
                let region = self.parse_region(r)?;
                Ok(self.arena.ty(Ty::Composable { arg, answer, effect, region, once }))
            }
            "bloblet" => {
                let [_, fields, r] = &items[..] else {
                    return Err(FxError::at(s.span, "`(bloblet (fields type …) region)`, or `(frozen type …)`"));
                };
                let parts = self.items(fields, "`(fields type …)`")?.to_vec();
                let frozen = match parts.first().and_then(|h| h.as_symbol()).map(|h| self.name(h)) {
                    Some("fields") => false,
                    Some("frozen") => true,
                    _ => return Err(FxError::at(fields.span, "`(fields type …)` or `(frozen type …)`")),
                };
                let fields = parts[1..].iter().map(|t| self.parse_type(t)).collect::<R<Vec<_>>>()?;
                let region = self.parse_region(r)?;
                Ok(self.arena.ty(Ty::Bloblet { fields, frozen, region }))
            }
            // A flat sum with a key (`TODO.md` §77), so `define-type` may
            // name one.
            "sumof" if items.get(1).is_some_and(|k| k.as_symbol().is_some()) => self.parse_flat(s),
            "productof" | "sumof" => {
                let mut parts = Vec::new();
                for p in &items[1..] {
                    let pair = self.items(p, "`(label type)`")?.to_vec();
                    let [label, t] = &pair[..] else {
                        return Err(FxError::at(p.span, "`(label type)`"));
                    };
                    let label = self.label(label)?;
                    if parts.iter().any(|(l, _)| *l == label) {
                        return Err(FxError::at(p.span, format!("`{}` appears twice", self.name(label))));
                    }
                    parts.push((label, self.parse_type(t)?));
                }
                let product = self.head(&items) == Some("productof");
                Ok(self.arena.ty(if product { Ty::Product(parts) } else { Ty::Sum(parts) }))
            }
            // `(moduleof (abs t type) … (desc d T) … (val x T) …)`: each
            // abstract type a binder, in scope in what follows it.
            "moduleof" => self.parse_moduleof(s.span, &items[1..]),
            "select" => {
                let [_, m, n] = &items[..] else {
                    return Err(FxError::at(s.span, "`(select module name)`"));
                };
                let (Some(m), Some(n)) = (m.as_symbol(), n.as_symbol()) else {
                    return Err(FxError::at(s.span, "`(select module name)`: a module's name, and a component's"));
                };
                Ok(self.arena.ty(Ty::Select(m, n)))
            }
            "arrayof" => {
                let [_, t, r] = &items[..] else {
                    return Err(FxError::at(s.span, "`(arrayof type region)`"));
                };
                // With a length, a literal or a size (`finite`, a size
                // variable, a sum of sizes), a flat array (`TODO.md` §77), so
                // a `define-type` may name one.
                if self.size_written(r) {
                    return self.parse_flat(s);
                }
                let t = self.parse_type(t)?;
                let r = self.parse_region(r)?;
                Ok(self.arena.ty(Ty::Array(t, Size::Finite, r)))
            }
            // `(narrayof type size region)`: an array of `size` elements.
            "narrayof" => {
                let [_, t, n, r] = &items[..] else {
                    return Err(FxError::at(s.span, "`(narrayof type size region)`"));
                };
                let t = self.parse_type(t)?;
                let n = self.parse_size(n)?;
                let r = self.parse_region(r)?;
                Ok(self.arena.ty(Ty::Array(t, n, r)))
            }
            // `(load-moduleof "file" arg …)`: the type of the module a
            // `load-module` of the file makes, given `arg …`;
            // `(load-input-moduleof "file" arg …)`, of the module a
            // `load-input` file's value makes (`docs/research/
            // derived-signatures.md`). The file is loaded as a load of it
            // is (`type_loads`), and nothing is made of it here.
            loader @ ("load-moduleof" | "load-input-moduleof") => {
                let input = loader == "load-input-moduleof";
                let usage = format!("`({loader} \"file\" argument …)`");
                let Some(Datum::Str(path)) = items.get(1).map(|p| &p.datum) else {
                    return Err(FxError::at(s.span, usage));
                };
                let path = path.clone();
                let name = self.load_name(s.span, &path, input)?;
                let Some(made) = self.lookup(name) else {
                    return Err(FxError::at(s.span, format!("`{path}` is not loaded here")));
                };
                // A file of module parameters is loaded as a `load-input`
                // file is (`modules_made`), its global's key so.
                let input = input || self.name(name).starts_with("%shared:input:");
                let made = if input { self.module_val(made, "input").expect("a `load-input` file's module gives `input`") } else { made };
                self.type_made(made, &items[2..], s.span, &path)
            }
            // `(restrict T name …)`: module type `T` with only the names
            // given (`docs/research/derived-signatures.md`, narrowing).
            "restrict" => self.restricted(s, &items),
            "mark-key" => {
                let [_, t, r] = &items[..] else {
                    return Err(FxError::at(s.span, "`(mark-key type region)`"));
                };
                let t = self.parse_type(t)?;
                let r = self.parse_region(r)?;
                Ok(self.arena.ty(Ty::MarkKey(t, r)))
            }
            // A name applied that is no description function: unbound, a
            // typo, or a type. In a module with `include`s, an unbound one
            // is the modules included's family, found when they are typed,
            // as a type's name is (`TODO.md` §69).
            _ => match items.first().and_then(|h| h.as_symbol()) {
                Some(h) if self.include_scope > 0 && self.lookup_desc(h).is_none() => {
                    let inc = self.interner.intern("%include");
                    let f = self.arena.ty(Ty::Select(inc, h));
                    self.parse_app(s, f, &items[1..])
                }
                Some(h) => Err(FxError::at(s.span, format!("`{}` is not a description function", self.name(h)))),
                None => Err(FxError::at(s.span, "expected a type")),
            },
        }
    }

    /// `(dletrec ((name type) …) type)`: recursive types, as cycles in the
    /// arena. Each name gets a forwarding slot before any body is parsed, so
    /// the bodies — and each other — can refer to it.
    fn parse_dletrec(&mut self, s: &Syntax, items: &[Syntax]) -> R<TyId> {
        let [_, bindings, body] = items else {
            return Err(FxError::at(s.span, "`(dletrec ((name type) …) type)`"));
        };
        let depth = self.dscope.len();
        let result = (|| {
            let mut slots = Vec::new();
            for b in self.items(bindings, "dletrec bindings")?.to_vec() {
                let pair = self.items(&b, "a dletrec binding")?.to_vec();
                let [name, def] = &pair[..] else {
                    return Err(FxError::at(b.span, "a dletrec binding is `(name type)`"));
                };
                let name = name.as_symbol().ok_or_else(|| FxError::at(name.span, "a name"))?;
                let slot = self.arena.ty(Ty::Link(None));
                self.dscope.push((name, DScope::Rec(slot)));
                slots.push((slot, def.clone()));
            }
            for (slot, def) in &slots {
                let t = self.parse_type(def)?;
                self.arena.set_link(*slot, t);
            }
            for (slot, _) in &slots {
                self.grounded(*slot, s.span)?;
            }
            for (slot, _) in &slots {
                self.no_knot(*slot, s.span)?;
            }
            self.parse_type(body)
        })();
        self.dscope.truncate(depth);
        result
    }

    /// Whether the recursive type at `slot`, its knot tied, is built from
    /// a constructor (`grounded_only`); and the unions read before it was,
    /// checked now that their members are known.
    pub(crate) fn grounded(&mut self, slot: TyId, span: fixpt_read::Span) -> R<()> {
        self.grounded_only(slot, span)?;
        self.check_pending_unions()
    }

    /// A name defined as another name, round a loop, describes nothing.
    fn grounded_only(&self, slot: TyId, span: fixpt_read::Span) -> R<()> {
        // A description function applied is no constructor either: what it
        // gives may be what it was given, so a cycle through applications
        // alone may be no type at all once the function is known (Rémy's
        // condition: recursion only at the base kind; `crate::kinds`).
        if self.through_apps(slot, slot, &mut std::collections::HashSet::new()) {
            return Err(FxError::at(span, "a recursive type must be built from a constructor, not only from names"));
        }
        let mut seen = std::collections::HashSet::new();
        let mut id = slot;
        loop {
            let next = match self.arena.get_raw(id) {
                // A `poly` is no constructor either: a cycle through `poly`s
                // alone describes no type, and unfolding it would never end.
                Ty::Link(Some(next)) | Ty::Poly { body: next, .. } => *next,
                // Nor is a generative type whose representation is one of
                // what it is given: it is that (`docs/research/
                // soundness-findings.md`, A2).
                Ty::Named { which, args } => match self.named_head(*which, args) {
                    Some(next) => next,
                    None => return Ok(()),
                },
                _ => return Ok(()),
            };
            if !seen.insert(id) {
                return Err(FxError::at(span, "a recursive type must be built from a constructor, not only from names"));
            }
            id = next;
        }
    }

    /// Whether `start` is reached again from `id` through forwarding links,
    /// `poly`s and the descriptions given to functions applied: a cycle
    /// with no constructor on it.
    fn through_apps(&self, id: TyId, start: TyId, seen: &mut std::collections::HashSet<TyId>) -> bool {
        if !seen.insert(id) {
            return false;
        }
        let next: Vec<TyId> = match self.arena.get_raw(id) {
            Ty::Link(Some(n)) => vec![*n],
            Ty::Poly { body, .. } => vec![*body],
            Ty::App { args, .. } => args.iter().filter_map(|d| if let D::Type(t) = d { Some(*t) } else { None }).collect(),
            _ => Vec::new(),
        };
        next.into_iter().any(|n| n == start || self.through_apps(n, start, seen))
    }

    /// The type the `which`th generative type, given `args`, is at its
    /// head, if its representation is one of its type parameters, perhaps
    /// through other such generative types: what it is given there. `None`
    /// if its representation has a constructor at its head.
    fn named_head(&self, mut which: u32, args: &[D]) -> Option<TyId> {
        let mut args = args.to_vec();
        let mut seen = std::collections::HashSet::new();
        while seen.insert(which) {
            let g = &self.generatives[which as usize];
            let param = |t: TyId| match self.arena.get(self.arena.resolve(t)) {
                Ty::Var(v) => g.params.iter().position(|(p, _)| p == v),
                _ => None,
            };
            match self.arena.get(self.arena.resolve(g.rep)) {
                Ty::Var(_) => {
                    return match args.get(param(g.rep)?) {
                        Some(D::Type(t)) => Some(*t),
                        _ => None,
                    };
                }
                Ty::Named { which: h, args: inner } => {
                    args = inner
                        .iter()
                        .map(|d| match d {
                            D::Type(t) => param(*t).and_then(|i| args.get(i).cloned()).unwrap_or(d.clone()),
                            _ => d.clone(),
                        })
                        .collect();
                    which = *h;
                }
                _ => return None,
            }
        }
        None
    }

    /// `(define-type (name (param kind) …) type)`: bind a parametric
    /// abbreviation. Nothing is parsed until it is used.
    pub(crate) fn define_type_family(&mut self, name: Sym, params: &Syntax, body: &Syntax) -> R<()> {
        let mut ps = Vec::new();
        for p in self.items(params, "`(name kind)`")?.to_vec() {
            let pair = self.items(&p, "`(name kind)`")?.to_vec();
            let [n, k] = &pair[..] else {
                return Err(FxError::at(p.span, "a parameter is `(name kind)`"));
            };
            let n = n.as_symbol().ok_or_else(|| FxError::at(n.span, "a parameter's name"))?;
            ps.push((n, self.parse_kind(k)?));
        }
        self.dscope.push((name, DScope::Abbrev { params: ps, body: body.clone() }));
        Ok(())
    }

    /// A use of a type family: its body, parsed with each parameter bound
    /// to the description given for it. A use inside the body with the same
    /// descriptions, as `(tree r)` in `tree`'s own, is the type being made:
    /// a knot, as `dletrec` ties. One with others expands again, so a
    /// family whose descriptions grow as it recurses never ends, and is
    /// stopped.
    fn expand_abbrev(&mut self, s: &Syntax, name: Sym, params: &[(Sym, Kind)], body: &Syntax, args: &[Syntax]) -> R<TyId> {
        if args.len() != params.len() {
            return Err(FxError::at(s.span, format!("`{}` takes {} description(s), and has {}", self.name(name), params.len(), args.len())));
        }
        if self.expanding > 64 {
            return Err(FxError::at(
                s.span,
                format!("`{}` expands without end: a type family may mention itself only with the same descriptions", self.name(name)),
            ));
        }
        let mut bound = Vec::new();
        let mut key = Vec::new();
        for ((p, k), a) in params.iter().zip(args) {
            let (d, arg) = match k {
                Kind::Type | Kind::Data | Kind::Sendable | Kind::Flat => {
                    let t = if *k == Kind::Flat { self.parse_flat(a)? } else { self.parse_type(a)? };
                    (DScope::Rec(t), crate::parse::FamilyArg::Ty(self.arena.resolve(t)))
                }
                Kind::Region | Kind::Place => {
                    let r = if *k == Kind::Region { self.parse_region(a)? } else { self.parse_place(a)? };
                    (DScope::Region(r), crate::parse::FamilyArg::Region(r))
                }
                Kind::Effect => {
                    let e = self.parse_effect(a)?;
                    (DScope::Eff(e.clone()), crate::parse::FamilyArg::Eff(e))
                }
                Kind::Size => {
                    let z = self.parse_size(a)?;
                    (DScope::SizeVal(z.clone()), crate::parse::FamilyArg::Size(z))
                }
                Kind::Conv => {
                    let c = self.parse_conv(a)?;
                    (DScope::ConvVal(c), crate::parse::FamilyArg::Conv(c))
                }
                Kind::Arrow(_) => {
                    let f = self.parse_fun(a, Some(*k))?;
                    (DScope::Fun(f), crate::parse::FamilyArg::Fun(self.arena.resolve(f)))
                }
            };
            bound.push((*p, d));
            key.push(arg);
        }
        if let Some((_, _, slot)) = self.knots.iter().rev().find(|(n, k, _)| *n == name && *k == key) {
            return Ok(*slot);
        }
        let slot = self.arena.ty(Ty::Link(None));
        self.knots.push((name, key, slot));
        let depth = self.dscope.len();
        self.dscope.extend(bound);
        self.expanding += 1;
        let r = self.parse_type(body);
        self.expanding -= 1;
        self.dscope.truncate(depth);
        self.knots.pop();
        let t = r?;
        self.arena.set_link(slot, t);
        self.grounded(slot, s.span)?;
        Ok(slot)
    }

    /// A size: a natural literal, `finite` (some number not known), a size
    /// variable, `(+ size …)`, or `(- size k)`.
    /// Whether `s` is written as a size, not a region: a natural literal,
    /// `finite`, a size variable or value, or `(+ …)` or `(- …)`.
    pub(crate) fn size_written(&self, s: &Syntax) -> bool {
        if self.literal_int(s).is_some_and(|k| k >= 0) {
            return true;
        }
        if let Some(x) = s.as_symbol() {
            return self.name(x) == "finite" || matches!(self.lookup_desc(x), Some(DScope::Var(_, Kind::Size) | DScope::SizeVal(_)));
        }
        matches!(s.as_proper_list().and_then(|l| l.first()).and_then(|h| h.as_symbol()).map(|h| self.name(h)), Some("+" | "-"))
    }

    pub(crate) fn parse_size(&mut self, s: &Syntax) -> R<Size> {
        let usage = "a size is a natural number, `finite`, a size variable, `(+ size …)` or `(- size k)`";
        if let Some(n) = self.literal_int(s)
            && n >= 0
        {
            return Ok(Size::lit(n));
        }
        if let Some(x) = s.as_symbol() {
            if self.name(x) == "finite" {
                return Ok(Size::Finite);
            }
            return match self.lookup_desc(x) {
                Some(DScope::Var(v, Kind::Size)) => Ok(Size::var(v)),
                Some(DScope::SizeVal(z)) => Ok(z),
                _ => Err(FxError::at(s.span, usage)),
            };
        }
        let items = self.items(s, "a size")?.to_vec();
        match (self.head(&items).unwrap_or(""), &items[..]) {
            ("+", [_, rest @ ..]) if !rest.is_empty() => {
                let mut out = Size::lit(0);
                for r in rest {
                    let z = self.parse_size(r)?;
                    out = out.add_scaled(&z, 1);
                }
                Ok(out)
            }
            ("-", [_, a, k]) => {
                let a = self.parse_size(a)?;
                match self.literal_int(k) {
                    Some(k) if k >= 0 => Ok(a.plus(-k)),
                    _ => Err(FxError::at(k.span, usage)),
                }
            }
            _ => Err(FxError::at(s.span, usage)),
        }
    }

    /// What `(proves prop)` states: its type, with the lemma kept pending.
    fn parse_proves(&mut self, prop: &Syntax, usage: &str) -> R<TyId> {
        let items = self.items(prop, "a proposition")?.to_vec();
        let (binders, conclusion, hyps) = match self.head(&items).unwrap_or("") {
            "poly" => match &items[..] {
                [_, bs, c, hs @ ..] => (self.parse_binders(bs)?, c.clone(), hs.to_vec()),
                _ => return Err(FxError::at(prop.span, usage)),
            },
            "<=" => (Vec::new(), prop.clone(), Vec::new()),
            _ => return Err(FxError::at(prop.span, usage)),
        };
        let le = |c: &mut Checker, s: &Syntax| -> R<(TyId, TyId)> {
            match c.items(s, "a proposition")?.to_vec().as_slice() {
                [h, a, b] if h.as_symbol().is_some_and(|h| c.name(h) == "<=") => Ok((c.parse_type(a)?, c.parse_type(b)?)),
                _ => Err(FxError::at(s.span, "a proposition is `(<= type type)`")),
            }
        };
        let (lhs, rhs) = le(self, &conclusion)?;
        let mut hs = Vec::new();
        for h in &hyps {
            hs.push(le(self, h)?);
        }
        let spin = Effect::atom(Atom::Spin);
        let mut params: Vec<TyId> =
            hs.iter().map(|(x, y)| self.arena.ty(Ty::Subr { conv: self.conv_default, effect: spin.clone(), params: vec![*x], result: *y, spec: None })).collect();
        params.push(lhs);
        let body = self.arena.ty(Ty::Subr { conv: self.conv_default, effect: spin, params, result: rhs, spec: None });
        let t = if binders.is_empty() { body } else { self.arena.ty(Ty::Poly { binders: binders.clone(), body }) };
        self.pending_lemma = Some(crate::lemma::Lemma { binders, lhs, rhs, hyps: hs, by: None });
        Ok(t)
    }

    /// `(name d …)` for the `g`th generative type: a node, never expanded.
    fn apply_generative(&mut self, s: &Syntax, g: u32, args: &[Syntax]) -> R<TyId> {
        let params = self.generatives[g as usize].params.clone();
        if args.len() != params.len() {
            let name = self.name(self.generatives[g as usize].name).to_string();
            return Err(FxError::at(s.span, format!("`{name}` takes {} description(s), and has {}", params.len(), args.len())));
        }
        let mut ds = Vec::new();
        for ((_, k), a) in params.iter().zip(args) {
            ds.push(match k {
                Kind::Type | Kind::Data | Kind::Sendable => D::Type(self.parse_type(a)?),
                Kind::Flat => D::Type(self.parse_flat(a)?),
                Kind::Region => D::Region(self.parse_region(a)?),
                Kind::Place => D::Region(self.parse_place(a)?),
                Kind::Effect => D::Effect(self.parse_effect(a)?),
                Kind::Size => D::Size(self.parse_size(a)?),
                Kind::Conv => D::Conv(self.parse_conv(a)?),
                Kind::Arrow(_) => D::Fun(self.parse_fun(a, Some(*k))?),
            });
        }
        let t = self.arena.ty(Ty::Named { which: g, args: ds });
        // What it holds may keep a procedure that reaches itself.
        self.no_knot(t, s.span)?;
        Ok(t)
    }

    /// `(define-generative (name (param kind [+|-]) …) rep)`, or with no
    /// parameters `(define-generative name rep)`: a new type, equal only to
    /// itself, whose values are `rep`'s, converted by `up-name` and
    /// `down-name`. A parameter is invariant unless marked `+` (covariant)
    /// or `-` (contravariant), which `rep` must bear out.
    pub(crate) fn define_generative(&mut self, head: &Syntax, rep: &Syntax) -> R<Sym> {
        let (name, params) = match head.as_proper_list() {
            Some([n, ps @ ..]) => (n, ps.to_vec()),
            _ => (head, Vec::new()),
        };
        let name = name.as_symbol().ok_or_else(|| FxError::at(name.span, "a generative type's name"))?;
        let depth = self.dscope.len();
        let mut binders = Vec::new();
        let mut declared = Vec::new();
        for p in &params {
            let (n, k, v) = match self.items(p, "a parameter")? {
                [n, k] => (n.clone(), k.clone(), Variance::Inv),
                [n, k, v] => {
                    let v = match v.as_symbol().map(|x| self.name(x)) {
                        Some("+") => Variance::Co,
                        Some("-") => Variance::Contra,
                        _ => return Err(FxError::at(v.span, "a parameter's variance is `+` or `-`")),
                    };
                    (n.clone(), k.clone(), v)
                }
                _ => return Err(FxError::at(p.span, "a parameter is `(name kind)`, `(name kind +)` or `(name kind -)`")),
            };
            let n = n.as_symbol().ok_or_else(|| FxError::at(n.span, "a parameter's name"))?;
            let kind = self.parse_kind(&k)?;
            if v != Variance::Inv && matches!(kind, Kind::Region | Kind::Place) {
                self.dscope.truncate(depth);
                return Err(FxError::at(p.span, "a region or place parameter is invariant: it names where data is"));
            }
            if v != Variance::Inv && matches!(kind, Kind::Arrow(_)) {
                self.dscope.truncate(depth);
                return Err(FxError::at(p.span, "a description function parameter is invariant"));
            }
            let dv = self.arena.dvar_of(n, kind);
            self.dscope.push((n, DScope::Var(dv, kind)));
            binders.push((dv, kind));
            declared.push(v);
        }
        let g = self.generatives.len() as u32;
        let slot = self.arena.ty(Ty::Link(None));
        self.generatives.push(crate::check::Generative { name, params: binders, variance: declared, rep: slot });
        // In scope in its own representation: recursion through the name.
        self.dscope.push((name, DScope::Generative(g)));
        let r = self.parse_type(rep);
        self.dscope.truncate(depth);
        let r = r?;
        self.arena.set_link(slot, r);
        self.check_variance(g, rep.span)?;
        self.dscope.push((name, DScope::Generative(g)));
        Ok(name)
    }

    /// `(define-type name type)`: `name` stands for the type from here on,
    /// and may appear in its own definition — a one-binding `dletrec` that
    /// stays in scope.
    pub(crate) fn define_type(&mut self, name: Sym, def: &Syntax, span: fixpt_read::Span) -> R<TyId> {
        // Declared ahead: its slot is in scope already; fill it, and check
        // it grounded once every slot is filled.
        if let Some(i) = self.ahead.iter().position(|(n, _)| *n == name) {
            let (_, slot) = self.ahead.remove(i);
            let t = self.parse_type(def)?;
            self.arena.set_link(slot, t);
            self.ahead_filled.push((slot, span));
            return Ok(slot);
        }
        let slot = self.arena.ty(Ty::Link(None));
        let depth = self.dscope.len();
        self.dscope.push((name, DScope::Rec(slot)));
        let r = self.parse_type(def).and_then(|t| {
            self.arena.set_link(slot, t);
            self.grounded(slot, span)
        });
        if r.is_err() {
            self.dscope.truncate(depth);
        }
        if r.is_ok() {
            self.note_closed(slot);
        }
        r.map(|()| slot)
    }

    /// `slot`, a type a `define-type` named, noted if it is data that
    /// mentions no variable: it keeps its name (`closed_named`). Once its
    /// knot is tied, or every slot declared ahead filled.
    pub(crate) fn note_closed(&mut self, slot: TyId) {
        if self.closed_data(slot, &mut std::collections::HashSet::new()) {
            self.closed_named.insert(self.arena.resolve(slot));
        }
    }

    /// Whether `s` is written as an effect: `pure`, `spin`, a name bound
    /// to one, or one of `parse_effect`'s atoms or `maxeff`.
    pub(crate) fn effect_shaped(&self, s: &Syntax) -> bool {
        if let Some(sym) = s.as_symbol() {
            return matches!(self.name(sym), "pure" | "spin" | "nondet") || matches!(self.lookup_desc(sym), Some(DScope::Eff(_) | DScope::Var(_, Kind::Effect)));
        }
        matches!(
            self.head(self.items(s, "").unwrap_or(&[])),
            Some("read" | "write" | "alloc" | "goto" | "comefrom" | "await" | "init" | "send" | "receive" | "io" | "maxeff")
        )
    }

    /// A `proj` argument. Which kind it is shows in its shape — `@x` is a
    /// region, `pure` and `(read …)`, `(maxeff …)` and the like are effects —
    /// or, for a bare name, in how the name is bound; the checker confirms it
    /// against the binder when it sees the `poly` being projected.
    pub(crate) fn parse_d(&mut self, s: &Syntax) -> R<D> {
        // A natural number can only be a size.
        if self.literal_int(s).is_some() {
            return Ok(D::Size(self.parse_size(s)?));
        }
        if let Some(sym) = s.as_symbol() {
            let name = self.name(sym);
            if name.starts_with('@') {
                return Ok(D::Region(self.region_constant(sym)));
            }
            if name == "pure" {
                return Ok(D::Effect(Effect::pure()));
            }
            if name == "spin" {
                return Ok(D::Effect(Effect::atom(Atom::Spin)));
            }
            if name == "nondet" {
                return Ok(D::Effect(Effect::atom(Atom::Nondet)));
            }
            if name == "const" {
                return Ok(D::Region(Region::Frozen(None, false)));
            }
            if name == "acyclic" {
                return Ok(D::Region(Region::Frozen(None, true)));
            }
            if name == "finite" {
                return Ok(D::Size(Size::Finite));
            }
            if name == "heap" {
                return Ok(D::Region(Region::Heap));
            }
            return match self.lookup_desc(sym) {
                Some(DScope::Var(_, Kind::Arrow(_)) | DScope::Fun(_)) => Ok(D::Fun(self.parse_fun(s, None)?)),
                Some(DScope::Abbrev { params, .. }) if !params.is_empty() => Ok(D::Fun(self.parse_fun(s, None)?)),
                Some(DScope::Generative(g)) if !self.generatives[g as usize].params.is_empty() => Ok(D::Fun(self.parse_fun(s, None)?)),
                None if crate::kinds::CONSTRUCTORS.iter().any(|(n, _)| *n == name) => Ok(D::Fun(self.parse_fun(s, None)?)),
                Some(DScope::Var(v, Kind::Region | Kind::Place)) => Ok(D::Region(Region::Var(v))),
                Some(DScope::Region(r)) => Ok(D::Region(r)),
                Some(DScope::Var(v, Kind::Effect)) => Ok(D::Effect(Effect::atom(Atom::Var(v)))),
                Some(DScope::Eff(e)) => Ok(D::Effect(e)),
                Some(DScope::Var(v, Kind::Size)) => Ok(D::Size(Size::var(v))),
                Some(DScope::SizeVal(z)) => Ok(D::Size(z)),
                Some(DScope::Var(v, Kind::Conv)) => Ok(D::Conv(Conv::Var(v))),
                Some(DScope::ConvVal(c)) => Ok(D::Conv(c)),
                _ if matches!(name, "cellular" | "native" | "fx") => Ok(D::Conv(self.parse_conv(s)?)),
                _ => Ok(D::Type(self.parse_type(s)?)),
            };
        }
        let items = self.items(s, "a description")?;
        match self.head(items).unwrap_or("") {
            "dlambda" => Ok(D::Fun(self.parse_fun(s, None)?)),
            "const" | "acyclic" => Ok(D::Region(self.parse_region(s)?)),
            "+" | "-" => Ok(D::Size(self.parse_size(s)?)),
            // Every atom `parse_effect` reads, as the FX-26 checker's
            // `k-atom-head?` (PLAN.md Q13, O15).
            "read" | "write" | "alloc" | "goto" | "comefrom" | "await" | "init" | "send" | "receive" | "io" | "maxeff" => {
                Ok(D::Effect(self.parse_effect(s)?))
            }
            _ => Ok(D::Type(self.parse_type(s)?)),
        }
    }

    // ---------------------------------------------------------- expressions
    /// An integer literal past a fixnum, `negative` and of `digits` in
    /// `radix`, as arithmetic on fixnums: `(- 0 x)` for a negative; else,
    /// in base 10⁹, `(+ (* rest 1000000000) last)`, `rest` again so until
    /// it is a fixnum. The FX-26 parser's `big-literal`, node for node.
    fn big_literal(&mut self, negative: bool, digits: &str, radix: u32, span: fixpt_read::Span) -> ExpId {
        // The value in base 10⁹, most significant limb first.
        let mut limbs: Vec<u64> = vec![0];
        for c in digits.chars() {
            let mut carry = c.to_digit(radix).unwrap_or(0) as u64;
            for l in limbs.iter_mut().rev() {
                let x = *l * radix as u64 + carry;
                *l = x % 1_000_000_000;
                carry = x / 1_000_000_000;
            }
            while carry > 0 {
                limbs.insert(0, carry % 1_000_000_000);
                carry /= 1_000_000_000;
            }
        }
        let value = |ls: &[u64]| -> Option<i128> {
            (ls.len() <= 4).then(|| ls.iter().fold(0i128, |v, l| v * 1_000_000_000 + *l as i128))
        };
        if let Some(v) = value(&limbs) {
            let v = if negative { -v } else { v };
            if (FIXNUM_MIN as i128..=FIXNUM_MAX as i128).contains(&v) {
                return self.arena.exp(span, Exp::Int(v as i64));
            }
        }
        let op = |p: &mut Self, name: &str, args: Vec<ExpId>| {
            let fun = p.arena.exp(span, Exp::Var(p.interner.intern(name)));
            p.arena.exp(span, Exp::App { fun, args })
        };
        if negative {
            let zero = self.arena.exp(span, Exp::Int(0));
            let x = self.big_literal(false, digits, radix, span);
            return op(self, "-", vec![zero, x]);
        }
        let (rest, last) = limbs.split_at(limbs.len() - 1);
        let rest_digits: String = if rest.is_empty() {
            "0".into()
        } else {
            rest.iter().enumerate().map(|(i, l)| if i == 0 { l.to_string() } else { format!("{l:09}") }).collect()
        };
        let hi = self.big_literal(false, &rest_digits, 10, span);
        let base = self.arena.exp(span, Exp::Int(1_000_000_000));
        let scaled = op(self, "*", vec![hi, base]);
        let lo = self.arena.exp(span, Exp::Int(last[0] as i64));
        op(self, "+", vec![scaled, lo])
    }

    pub fn parse_exp(&mut self, s: &Syntax) -> R<ExpId> {
        let span = s.span;
        match &s.datum {
            Datum::Number(fixpt_read::Num::Int(n)) if (FIXNUM_MIN..=FIXNUM_MAX).contains(n) => return Ok(self.arena.exp(span, Exp::Int(*n))),
            // An integer literal past a fixnum: arithmetic on fixnums, which
            // every path does, bignums included (PLAN.md Q2).
            Datum::Number(fixpt_read::Num::Int(n)) => {
                let digits = (*n as i128).unsigned_abs().to_string();
                return Ok(self.big_literal(*n < 0, &digits, 10, span));
            }
            Datum::Number(fixpt_read::Num::Big { negative, digits, radix }) => return Ok(self.big_literal(*negative, digits, *radix, span)),
            Datum::Str(t) => return Ok(self.arena.exp(span, Exp::Str(t.clone()))),
            Datum::Bool(b) => return Ok(self.arena.exp(span, Exp::Bool(*b))),
            Datum::Char(c) => return Ok(self.arena.exp(span, Exp::Char(*c))),
            Datum::Number(fixpt_read::Num::Real(x)) => return Ok(self.arena.exp(span, Exp::Float(*x))),
            Datum::Symbol(sym) => {
                // `#u` reads as a symbol; `#t` and `#f` did too in FX-87's
                // profile, which FX-26 used to be read with.
                let e = match self.name(*sym) {
                    "#t" => Exp::Bool(true),
                    "#f" => Exp::Bool(false),
                    "#u" => Exp::Unit,
                    _ => Exp::Var(*sym),
                };
                return Ok(self.arena.exp(span, e));
            }
            Datum::List { .. } => {}
            _ => return Err(FxError::at(span, "not an expression in the FX-26 kernel")),
        }
        let items = self.items(s, "an expression")?;
        match self.head(&items).unwrap_or("") {
            "lambda" => {
                let [_, params, body @ ..] = &items[..] else {
                    return Err(FxError::at(span, "`(lambda ((name type) …) body …)`"));
                };
                self.parse_lambda(span, params, body)
            }
            // A variadic procedure, FX-87's: `(vlambda xs body …)`, or with
            // the arguments' type, `(vlambda (xs T) body …)`, is
            // `(%vlambda (lambda ((xs (listof T acyclic))) body …))`, the
            // procedure of the list of its arguments made a `vsubr`.
            "vlambda" => {
                let [_, param, body @ ..] = &items[..] else {
                    return Err(FxError::at(span, "`(vlambda name body …)` or `(vlambda (name type) body …)`"));
                };
                let sym = |p: &mut Self, s: &str| Syntax::symbol(span, p.interner.intern(s));
                let param = match param.as_proper_list() {
                    Some([name, t]) => {
                        let list = Syntax::list(span, vec![sym(self, "listof"), t.clone(), sym(self, "acyclic")]);
                        Syntax::list(span, vec![name.clone(), list])
                    }
                    _ if param.as_symbol().is_some() => param.clone(),
                    _ => return Err(FxError::at(param.span, "`(vlambda name body …)` or `(vlambda (name type) body …)`")),
                };
                let mut lambda = vec![sym(self, "lambda"), Syntax::list(span, vec![param])];
                lambda.extend(body.iter().cloned());
                let call = Syntax::list(span, vec![sym(self, "%vlambda"), Syntax::list(span, lambda)]);
                self.parse_exp(&call)
            }
            "rlambda" => {
                let [_, region, params, body @ ..] = &items[..] else {
                    return Err(FxError::at(span, "`(rlambda region ((name type) …) body …)`"));
                };
                let region = self.parse_exp(region)?;
                let lambda = self.parse_lambda(span, params, body)?;
                Ok(self.arena.exp(span, Exp::RLambda { region, lambda }))
            }
            "plambda" => {
                let [_, binders, body @ ..] = &items[..] else {
                    return Err(FxError::at(span, "`(plambda ((name kind) …) body …)`"));
                };
                let (depth, lives) = (self.dscope.len(), self.lifetimes.len());
                // A procedure's regions and places outlive whatever its body
                // binds.
                let parsed = self.parse_binders(binders).and_then(|b| {
                    for (v, k) in &b {
                        if matches!(k, Kind::Region | Kind::Place) {
                            self.arena.set_outer(*v, self.lifetimes[..lives].to_vec());
                            self.lifetimes.push(*v);
                        }
                    }
                    Ok((b, self.parse_body(span, body)?))
                });
                self.dscope.truncate(depth);
                self.lifetimes.truncate(lives);
                let (binders, body) = parsed?;
                Ok(self.arena.exp(span, Exp::PLambda { binders, body }))
            }
            "proj" => {
                let [_, body, args @ ..] = &items[..] else {
                    return Err(FxError::at(span, "`(proj expression description …)`"));
                };
                if args.is_empty() {
                    return Err(FxError::at(span, "`proj` needs at least one description"));
                }
                let body = self.parse_exp(body)?;
                let args = args.iter().map(|a| self.parse_d(a)).collect::<R<Vec<_>>>()?;
                Ok(self.arena.exp(span, Exp::Proj { body, args }))
            }
            "if" => {
                let [_, test, then, els] = &items[..] else {
                    return Err(FxError::at(span, "`(if test then else)`"));
                };
                let (test, then, els) = (self.parse_exp(test)?, self.parse_exp(then)?, self.parse_exp(els)?);
                Ok(self.arena.exp(span, Exp::If { test, then, els }))
            }
            "letrec" => {
                let [_, bindings, body @ ..] = &items[..] else {
                    return Err(FxError::at(span, "`(letrec ((name type expression) …) body …)`"));
                };
                let mut out = Vec::new();
                for b in self.items(bindings, "letrec bindings")? {
                    let parts = self.items(b, "a letrec binding")?;
                    let [name, ty, init] = &parts[..] else {
                        return Err(FxError::at(b.span, "a letrec binding is `(name type expression)`"));
                    };
                    let name = name.as_symbol().ok_or_else(|| FxError::at(name.span, "a name"))?;
                    self.arrow_star = self.written_arrow_star(ty);
                    out.push((name, self.parse_type(ty)?, self.parse_exp(init)?));
                }
                let body = self.parse_body(span, body)?;
                Ok(self.arena.exp(span, Exp::Letrec { bindings: out, body }))
            }
            "let" => {
                let [_, bindings, body @ ..] = &items[..] else {
                    return Err(FxError::at(span, "`(let ((name expression) …) body …)`"));
                };
                let mut out = Vec::new();
                let bs = match &bindings.datum {
                    Datum::Nil => &[][..],
                    _ => self.items(bindings, "let bindings")?,
                };
                for b in bs {
                    let parts = self.items(b, "a let binding")?;
                    let [name, init] = &parts[..] else {
                        return Err(FxError::at(b.span, "a let binding is `(name expression)`"));
                    };
                    let name = name.as_symbol().ok_or_else(|| FxError::at(name.span, "a name"))?;
                    out.push((name, self.parse_exp(init)?));
                }
                let body = self.parse_body(span, body)?;
                Ok(self.arena.exp(span, Exp::Let { bindings: out, body }))
            }
            "begin" => self.parse_body(span, &items[1..]),
            // A syscall declared (`syscall.rs`): its hidden global, whether
            // the runtime has it.
            "syscall-available?" => {
                let asked = self.syscall_available_form(s, items)?;
                self.parse_exp(&asked)
            }
            // Processes and `par` (`processes.rs`).
            head @ ("spawn" | "spawn-monitored" | "send" | "receive" | "self" | "par" | "race" | "attempt" | "pselect" | "icell-get" | "icell-put!") => {
                let head = head.to_string();
                self.parse_process_form(span, &head, &items)
            }
            "cond" => self.parse_cond(span, &items[1..]),
            "case" => self.parse_case(span, &items[1..]),
            "typecase" => self.parse_typecase(span, &items),
            // `(acyclic e (x body) else)`: `(let ((%acyclic-value e)) (if
            // (acyclic? %acyclic-value) (let ((x (certify-acyclic
            // %acyclic-value))) body) else))`.
            // `(confirm-length e k (x body) else)`: `(let ((%confirm-value
            // e)) (if (length-is? %confirm-value k) (let ((x (certify-length
            // %confirm-value k))) body) else))`.
            "confirm-length" => {
                let usage = "`(confirm-length expression length (name body) else)`";
                let [_, e, n, arm, els] = &items[..] else {
                    return Err(FxError::at(span, usage));
                };
                // A natural literal, or a variable holding a `nat`.
                let k = match (self.literal_int(n), n.as_symbol()) {
                    (Some(k), _) if k >= 0 => Exp::Int(k),
                    (None, Some(v)) => Exp::Var(v),
                    _ => return Err(FxError::at(n.span, "a length is a natural number, or a variable holding one")),
                };
                let [x, body] = self.items(arm, usage)? else {
                    return Err(FxError::at(arm.span, usage));
                };
                let x = x.as_symbol().ok_or_else(|| FxError::at(x.span, "a name"))?;
                let (e, body, els) = (self.parse_exp(e)?, self.parse_exp(body)?, self.parse_exp(els)?);
                let var = |c: &mut Checker, n: &str| c.standard_ref_at(span, n);
                let tmp = self.fresh_name("%confirm-value", &items);
                let a = self.arena.exp(span, Exp::Var(tmp));
                let (f, l) = (var(self, "length-is?"), self.arena.exp(span, k.clone()));
                let test = self.arena.exp(span, Exp::App { fun: f, args: vec![a, l] });
                let a = self.arena.exp(span, Exp::Var(tmp));
                let (f, l) = (var(self, "certify-length"), self.arena.exp(span, k));
                let cert = self.arena.exp(span, Exp::App { fun: f, args: vec![a, l] });
                let then = self.arena.exp(span, Exp::Let { bindings: vec![(x, cert)], body });
                let branch = self.arena.exp(span, Exp::If { test, then, els });
                Ok(self.arena.exp(span, Exp::Let { bindings: vec![(tmp, e)], body: branch }))
            }
            "acyclic" => {
                let usage = "`(acyclic expression (name body) else)`";
                let [_, e, arm, els] = &items[..] else {
                    return Err(FxError::at(span, usage));
                };
                let [x, body] = self.items(arm, usage)? else {
                    return Err(FxError::at(arm.span, usage));
                };
                let x = x.as_symbol().ok_or_else(|| FxError::at(x.span, "a name"))?;
                let (e, body, els) = (self.parse_exp(e)?, self.parse_exp(body)?, self.parse_exp(els)?);
                let var = |c: &mut Checker, n: &str| c.standard_ref_at(span, n);
                let tmp = self.fresh_name("%acyclic-value", &items);
                let (test_f, test_a) = (var(self, "acyclic?"), self.arena.exp(span, Exp::Var(tmp)));
                let test = self.arena.exp(span, Exp::App { fun: test_f, args: vec![test_a] });
                let (cert_f, cert_a) = (var(self, "certify-acyclic"), self.arena.exp(span, Exp::Var(tmp)));
                let cert = self.arena.exp(span, Exp::App { fun: cert_f, args: vec![cert_a] });
                let then = self.arena.exp(span, Exp::Let { bindings: vec![(x, cert)], body });
                let branch = self.arena.exp(span, Exp::If { test, then, els });
                Ok(self.arena.exp(span, Exp::Let { bindings: vec![(tmp, e)], body: branch }))
            }
            // `(confirm-nat e (n body) else)`: `(let ((%nat-value e)) (if
            // (nat? %nat-value) (let ((n (certify-nat %nat-value))) body)
            // else))`.
            "confirm-nat" => {
                let usage = "`(confirm-nat expression (name body) else)`";
                let [_, e, arm, els] = &items[..] else {
                    return Err(FxError::at(span, usage));
                };
                let [x, body] = self.items(arm, usage)? else {
                    return Err(FxError::at(arm.span, usage));
                };
                let x = x.as_symbol().ok_or_else(|| FxError::at(x.span, "a name"))?;
                let (e, body, els) = (self.parse_exp(e)?, self.parse_exp(body)?, self.parse_exp(els)?);
                let var = |c: &mut Checker, n: &str| c.standard_ref_at(span, n);
                let tmp = self.fresh_name("%nat-value", &items);
                let (test_f, test_a) = (var(self, "nat?"), self.arena.exp(span, Exp::Var(tmp)));
                let test = self.arena.exp(span, Exp::App { fun: test_f, args: vec![test_a] });
                let (cert_f, cert_a) = (var(self, "certify-nat"), self.arena.exp(span, Exp::Var(tmp)));
                let cert = self.arena.exp(span, Exp::App { fun: cert_f, args: vec![cert_a] });
                let then = self.arena.exp(span, Exp::Let { bindings: vec![(x, cert)], body });
                let branch = self.arena.exp(span, Exp::If { test, then, els });
                Ok(self.arena.exp(span, Exp::Let { bindings: vec![(tmp, e)], body: branch }))
            }
            "and" => {
                // `(and a b …)`: `(if a (and b …) #f)`, and `(and)` is `#t`.
                let mut out = self.arena.exp(span, Exp::Bool(true));
                for (i, x) in items[1..].iter().enumerate().rev() {
                    let x = self.parse_exp(x)?;
                    out = if i == items.len() - 2 {
                        x
                    } else {
                        let f = self.arena.exp(span, Exp::Bool(false));
                        self.arena.exp(span, Exp::If { test: x, then: out, els: f })
                    };
                }
                Ok(out)
            }
            "or" => {
                // `(or a b …)`: `(if a #t (or b …))`, and `(or)` is `#f`. On
                // booleans only, so `#t` loses nothing.
                let mut out = self.arena.exp(span, Exp::Bool(false));
                for (i, x) in items[1..].iter().enumerate().rev() {
                    let x = self.parse_exp(x)?;
                    out = if i == items.len() - 2 {
                        x
                    } else {
                        let t = self.arena.exp(span, Exp::Bool(true));
                        self.arena.exp(span, Exp::If { test: x, then: t, els: out })
                    };
                }
                Ok(out)
            }
            "let*" => {
                let [_, bindings, body @ ..] = &items[..] else {
                    return Err(FxError::at(span, "`(let* ((name expression) …) body …)`"));
                };
                let bs = match &bindings.datum {
                    Datum::Nil => &[][..],
                    _ => self.items(bindings, "let* bindings")?,
                };
                let mut parsed = Vec::new();
                for b in bs {
                    let parts = self.items(b, "a let* binding")?;
                    let [name, init] = &parts[..] else {
                        return Err(FxError::at(b.span, "a let* binding is `(name expression)`"));
                    };
                    let name = name.as_symbol().ok_or_else(|| FxError::at(name.span, "a name"))?;
                    parsed.push((name, self.parse_exp(init)?, b.span));
                }
                let mut out = self.parse_body(span, body)?;
                for (name, init, bspan) in parsed.into_iter().rev() {
                    out = self.arena.exp(bspan, Exp::Let { bindings: vec![(name, init)], body: out });
                }
                Ok(out)
            }
            "the" => {
                let [_, ty, exp] = &items[..] else {
                    return Err(FxError::at(span, "`(the type expression)`"));
                };
                let ty = self.parse_type(ty)?;
                let exp = self.parse_exp(exp)?;
                Ok(self.arena.exp(span, Exp::The { ty, exp }))
            }
            "convention" => {
                let [_, conv, exp] = &items[..] else {
                    return Err(FxError::at(span, "`(convention C expression)`"));
                };
                let conv = self.parse_conv(conv)?;
                let exp = self.parse_exp(exp)?;
                Ok(self.arena.exp(span, Exp::Convention { conv, exp }))
            }
            name if BlobletOp::NAMES.contains(&name) => {
                let name = name.to_string();
                self.parse_bloblet(span, &name, &items[1..])
            }
            "module" => self.parse_module(span, &items[1..]),
            // `(extend e0 e1)` (FX-91's, `TODO.md` §69): a module of the two,
            // `%extend-0` and `%extend-1`, whose values the checker makes it
            // of, `e1`'s where both have a name (`Checker::extended`). `e1`
            // sees `e0`'s bindings, `(with %extend-0 e1)`, as FX-91's.
            "extend" => {
                let [_, e0, e1] = &items[..] else {
                    return Err(FxError::at(span, "`(extend module module)`"));
                };
                let names = [self.interner.intern("%extend-0"), self.interner.intern("%extend-1")];
                let e0 = self.parse_exp(e0)?;
                let e1 = self.with_types_of(names[0], |p| p.parse_exp(e1))?;
                // Made at the form.
                let e1 = self.arena.exp(span, Exp::With { module: names[0], body: e1 });
                let items = vec![
                    ModItem::Val { name: names[0], ty: None, init: e0, infer: false },
                    ModItem::Val { name: names[1], ty: None, init: e1, infer: false },
                ];
                Ok(self.arena.exp(span, Exp::Module(items)))
            }
            // `(load-module "file")`: the file's forms, a module's items,
            // seeing only the standard environment (M7). `(load-input
            // "file")`: the file's one expression, Sheldon's `input`.
            loader @ ("load-module" | "load-input") => {
                let input = loader == "load-input";
                let [_, path] = &items[..] else {
                    return Err(FxError::at(span, format!("`({loader} \"file\")`")));
                };
                let Datum::Str(path) = &path.datum else {
                    return Err(FxError::at(path.span, format!("`({loader} \"file\")`: the file's name, as a string")));
                };
                self.parse_load(span, path, input)
            }
            // `(%loaded "key" "path")`: the module of the file `key` names,
            // `path` as a load wrote it (`parse_loaded`).
            "%loaded" => {
                let [_, key, path] = &items[..] else {
                    return Err(FxError::at(span, "`(%loaded \"key\" \"path\")`"));
                };
                let (Datum::Str(key), Datum::Str(path)) = (&key.datum, &path.datum) else {
                    return Err(FxError::at(span, "`(%loaded \"key\" \"path\")`"));
                };
                self.parse_loaded(span, key, path)
            }
            "with" => {
                let [_, m, body @ ..] = &items[..] else {
                    return Err(FxError::at(span, "`(with module body …)`"));
                };
                let module = m.as_symbol().ok_or_else(|| FxError::at(m.span, "`with` opens a module named by a variable"))?;
                let body = self.with_types_of(module, |p| p.parse_body(span, body))?;
                Ok(self.arena.exp(span, Exp::With { module, body }))
            }
            "product" => {
                let mut fields = Vec::new();
                for p in &items[1..] {
                    let pair = self.items(p, "`(label expression)`")?.to_vec();
                    let [label, e] = &pair[..] else {
                        return Err(FxError::at(p.span, "`(product (label expression) …)`"));
                    };
                    let label = self.label(label)?;
                    if fields.iter().any(|(l, _)| *l == label) {
                        return Err(FxError::at(p.span, format!("`{}` appears twice", self.name(label))));
                    }
                    fields.push((label, self.parse_exp(e)?));
                }
                Ok(self.arena.exp(span, Exp::Product(fields)))
            }
            "extract" => {
                let [_, e, label] = &items[..] else {
                    return Err(FxError::at(span, "`(extract expression label)`"));
                };
                let label = self.label(label)?;
                let e = self.parse_exp(e)?;
                Ok(self.arena.exp(span, Exp::Extract(e, label)))
            }
            "sum" => {
                // `(sum ⟨hole⟩)`: the hole is a tag; the payload, nothing yet.
                if let (Some(h), [_, tag]) = (self.holes, &items[..])
                    && tag.as_symbol() == Some(h.exp)
                {
                    let unit = self.arena.exp(span, Exp::Unit);
                    return Ok(self.arena.exp(span, Exp::Sum(h.tag, unit)));
                }
                let [_, tag, e] = &items[..] else {
                    return Err(FxError::at(span, "`(sum tag expression)`"));
                };
                let tag = self.label(tag)?;
                let e = self.parse_exp(e)?;
                Ok(self.arena.exp(span, Exp::Sum(tag, e)))
            }
            "tagcase" => self.parse_tagcase(span, &items[1..]),
            "quote" => match &items[..] {
                [_, x] if x.as_symbol().is_some() => Ok(self.arena.exp(span, Exp::Symbol(x.as_symbol().expect("a symbol")))),
                [_, x] => {
                    Self::no_bytevector(x)?;
                    let built = self.quoted(x, None);
                    self.parse_exp(&built)
                }
                _ => Err(FxError::at(span, "`(quote datum)`")),
            },
            "quasiquote" => match &items[..] {
                [_, x] => {
                    Self::no_bytevector(x)?;
                    let built = self.quoted(x, Some(1));
                    self.parse_exp(&built)
                }
                _ => Err(FxError::at(span, "`(quasiquote datum)`")),
            },
            form @ ("letregion" | "letfreeze" | "letrena" | "letreap") => {
                let [_, name, body @ ..] = &items[..] else {
                    return Err(FxError::at(span, format!("`({form} name body …)`")));
                };
                // `(letfreeze (r p) body …)` freezes into place `p`;
                // `(letfreeze r body …)` into the heap.
                let (name, into) = match name.as_proper_list() {
                    Some([n, p]) if form == "letfreeze" => (n, Some(self.parse_place(p)?)),
                    _ => (name, None),
                };
                let name = name.as_symbol().filter(|n| !self.name(*n).starts_with('@')).ok_or_else(|| {
                    FxError::at(name.span, format!("a `{form}` binds a region variable's name, without `@`"))
                })?;
                let form = match form {
                    "letregion" => RegionForm::Region,
                    "letfreeze" => RegionForm::Freeze(match into {
                        Some(Region::Var(p)) => Some(p),
                        _ => None,
                    }),
                    "letrena" => RegionForm::Arena,
                    _ => RegionForm::Reap,
                };
                let depth = self.dscope.len();
                // `letrena` and `letreap` make a place (which is also a
                // region), `letregion` a region only.
                let kind = if matches!(form, RegionForm::Region | RegionForm::Freeze(_)) { Kind::Region } else { Kind::Place };
                let region = self.arena.dvar_of(name, kind);
                // Fresh, so it aliases nothing (Lucassen's `PRIVATE`).
                self.arena.set_distinct(region);
                // A `letfreeze`'s data leaves in the place it freezes into, so
                // it may be allocated only in that place or one outliving it:
                // those are all it won't outlive.
                let outer = match form {
                    RegionForm::Freeze(Some(p)) => [p].into_iter().chain(self.arena.outer(p).iter().copied()).collect(),
                    RegionForm::Freeze(None) => Vec::new(),
                    _ => self.lifetimes.clone(),
                };
                self.arena.set_outer(region, outer);
                self.dscope.push((name, DScope::Var(region, kind)));
                self.lifetimes.push(region);
                let body = self.parse_body(span, body);
                self.lifetimes.pop();
                self.dscope.truncate(depth);
                Ok(self.arena.exp(span, Exp::LetRegion { form, region, body: body? }))
            }
            "prompt" => {
                let [_, tag, body, handler] = &items[..] else {
                    return Err(FxError::at(span, "`(prompt tag body handler)`"));
                };
                let (tag, body, handler) = (self.parse_exp(tag)?, self.parse_exp(body)?, self.parse_exp(handler)?);
                Ok(self.arena.exp(span, Exp::Prompt { tag, body, handler }))
            }
            _ => {
                let fun = self.parse_exp(&items[0])?;
                let args = items[1..].iter().map(|a| self.parse_exp(a)).collect::<R<Vec<_>>>()?;
                Ok(self.arena.exp(span, Exp::App { fun, args }))
            }
        }
    }

    /// `(cond (test e …) … (else e …))`: nested `if`s. FX has no unspecified
    /// value, so the `else` is required.
    fn parse_cond(&mut self, span: fixpt_read::Span, clauses: &[Syntax]) -> R<ExpId> {
        let Some((last, init)) = clauses.split_last() else {
            return Err(FxError::at(span, "a `cond` needs at least an `else` clause"));
        };
        let parts = self.items(last, "a cond clause")?.to_vec();
        if parts.first().and_then(|h| h.as_symbol()).map(|h| self.name(h)) != Some("else") {
            return Err(FxError::at(last.span, "a `cond` must end with an `else` clause: FX has no unspecified value"));
        }
        let mut out = self.parse_body(last.span, &parts[1..])?;
        for c in init.iter().rev() {
            let parts = self.items(c, "a cond clause")?.to_vec();
            let [test, body @ ..] = &parts[..] else {
                return Err(FxError::at(c.span, "a cond clause is `(test expression …)`"));
            };
            let test = self.parse_exp(test)?;
            let then = self.parse_body(c.span, body)?;
            out = self.arena.exp(c.span, Exp::If { test, then, els: out });
        }
        Ok(out)
    }

    /// `(with #%fx name)`: what an expansion calls, the standard binding,
    /// whatever shadows or redefines `name` where it is (`TODO.md` §46).
    fn standard_ref_at(&mut self, span: fixpt_read::Span, name: &str) -> ExpId {
        let s = self.interner.intern(name);
        let body = self.arena.exp(span, Exp::Var(s));
        let module = self.interner.intern("#%fx");
        self.arena.exp(span, Exp::With { module, body })
    }

    /// `(typecase e (shape name body) … (else name body))` on a union's members
    /// (`docs/research/logical-types.md`, L1): `(let ((%typecase-value e))
    /// (if (int? %typecase-value) (let ((name %typecase-value)) body) …
    /// else))`, each arm's test its shape's standard predicate, which narrows
    /// the value for the arm and for those after it (a variable tested as it
    /// is). The `else` is required, as `case`'s is.
    fn parse_typecase(&mut self, span: fixpt_read::Span, items: &[Syntax]) -> R<ExpId> {
        let usage = "`(typecase expression (shape name body) … (else name body))`";
        let [_, e, arms @ ..] = items else {
            return Err(FxError::at(span, usage));
        };
        let Some((last, init)) = arms.split_last() else {
            return Err(FxError::at(span, "a `typecase` needs at least an `else` clause"));
        };
        // A variable, which nothing assigns, is tested as it is, so that
        // what each test narrows it to holds of it in the arms after; any
        // other expression is bound once.
        let direct = e.as_symbol().filter(|s| !matches!(self.name(*s), "#t" | "#f" | "#u"));
        let (tmp, e) = match direct {
            Some(s) => (s, None),
            None => (self.fresh_name("%typecase-value", items), Some(self.parse_exp(e)?)),
        };
        let mut tests = Vec::new();
        for arm in init {
            let parts = self.items(arm, usage)?.to_vec();
            let [shape, x, body] = &parts[..] else {
                return Err(FxError::at(arm.span, usage));
            };
            let name = shape.as_symbol().map(|s| self.name(s).to_string());
            let Some(pred) = name.and_then(|n| typecase_predicate(&n)) else {
                let shapes: Vec<&str> = TYPECASE_SHAPES.iter().map(|(s, _)| *s).collect();
                return Err(FxError::at(shape.span, format!("a shape `typecase` tests is one of {}", shapes.join(", "))));
            };
            let x = x.as_symbol().ok_or_else(|| FxError::at(x.span, "a name"))?;
            tests.push((pred, x, self.parse_exp(body)?));
        }
        // `(else body)`, or `(else name body)`, `name` the value as what
        // the arms leave it.
        let parts = self.items(last, usage)?.to_vec();
        let else_usage = "a `typecase` must end with an `else` clause, `(else body)` or `(else name body)`";
        let (head, name, body) = match &parts[..] {
            [head, body] => (head, None, body),
            [head, name, body] => (head, Some(name.as_symbol().ok_or_else(|| FxError::at(name.span, "a name"))?), body),
            _ => return Err(FxError::at(last.span, else_usage)),
        };
        if head.as_symbol().map(|h| self.name(h)) != Some("else") {
            return Err(FxError::at(last.span, else_usage));
        }
        let mut chain = self.parse_exp(body)?;
        if let Some(x) = name {
            let v = self.arena.exp(span, Exp::Var(tmp));
            chain = self.arena.exp(span, Exp::Let { bindings: vec![(x, v)], body: chain });
        }
        for (pred, x, body) in tests.into_iter().rev() {
            let f = self.standard_ref_at(span, pred);
            let a = self.arena.exp(span, Exp::Var(tmp));
            let test = self.arena.exp(span, Exp::App { fun: f, args: vec![a] });
            let v = self.arena.exp(span, Exp::Var(tmp));
            let then = self.arena.exp(span, Exp::Let { bindings: vec![(x, v)], body });
            chain = self.arena.exp(span, Exp::If { test, then, els: chain });
        }
        Ok(match e {
            Some(e) => self.arena.exp(span, Exp::Let { bindings: vec![(tmp, e)], body: chain }),
            None => chain,
        })
    }

    /// `(bool (then P …) (else Q …))`, the result of a procedure of `n`
    /// parameters: a `bool` that proves each `P` of its arguments where it is
    /// true, each `Q` where false, a proposition `(shape i shape)` or `(not
    /// (shape i shape))`, `i` a parameter's number from 0; what it ensures
    /// (`crate::specs::latent`).
    fn parse_proving(&mut self, s: &Syntax, n: usize) -> R<crate::logic::Formula<crate::ast::Named>> {
        let usage = "`(bool (then proposition …) (else proposition …))`";
        let items = self.items(s, usage)?.to_vec();
        let [_, then, els] = &items[..] else {
            return Err(FxError::at(s.span, usage));
        };
        let then = self.parse_props(then, "then", n)?;
        let els = self.parse_props(els, "else", n)?;
        Ok(crate::specs::latent(&then, &els))
    }

    fn parse_props(&mut self, s: &Syntax, which: &str, n: usize) -> R<Vec<crate::ast::Prop>> {
        let usage = format!("`({which} proposition …)`");
        let items = self.items(s, &usage)?.to_vec();
        if items.first().and_then(|h| h.as_symbol()).map(|h| self.name(h)) != Some(which) {
            return Err(FxError::at(s.span, usage));
        }
        items[1..].iter().map(|p| self.parse_prop(p, n)).collect()
    }

    /// A proposition (`crate::ast::Prop`), of a procedure of `n`
    /// parameters.
    fn parse_prop(&mut self, p: &Syntax, n: usize) -> R<crate::ast::Prop> {
        use crate::ast::{Prop, Rel};
        let usage = "a proposition: `(shape i shape)`, `(acyclic i)`, `(nat i)`, `(length i j)`, `(< a b)`, `(<= a b)`, `(= a b)`, or `(not …)` of a shape or an `=`";
        let parts = self.items(p, usage)?.to_vec();
        let head = |c: &Self, x: &Syntax| x.as_symbol().map(|h| c.name(h).to_string());
        let (negated, form) = match &parts[..] {
            [h, inner] if head(self, h).as_deref() == Some("not") => (true, inner.clone()),
            _ => (false, p.clone()),
        };
        let parts = self.items(&form, usage)?.to_vec();
        let name = parts.first().and_then(|h| head(self, h)).unwrap_or_default();
        match (name.as_str(), &parts[1..], negated) {
            ("shape", [i, k], _) => {
                let param = self.prop_param(i, n)?;
                let Some(shape) = head(self, k).and_then(|k| crate::check::SHAPES.iter().position(|(s, _)| *s == k)) else {
                    let shapes: Vec<&str> = crate::check::SHAPES.iter().map(|(s, _)| *s).collect();
                    return Err(FxError::at(k.span, format!("a shape, one of {}", shapes.join(", "))));
                };
                Ok(Prop::Shape { param, shape, negated })
            }
            ("acyclic", [i], false) => Ok(Prop::Acyclic(self.prop_param(i, n)?)),
            ("nat", [i], false) => Ok(Prop::Nat(self.prop_param(i, n)?)),
            ("length", [i, j], false) => {
                let i = self.prop_param(i, n)?;
                Ok(Prop::Length(i, self.prop_param(j, n)?))
            }
            (r @ ("<" | "<=" | "="), [x, y], not) if !not || r == "=" => {
                let a = self.prop_term(x, n)?;
                let b = self.prop_term(y, n)?;
                let op = match (r, not) {
                    ("<", _) => Rel::Lt,
                    ("<=", _) => Rel::Le,
                    (_, false) => Rel::Eq,
                    _ => Rel::Ne,
                };
                Ok(Prop::Rel { op, a, b })
            }
            _ => Err(FxError::at(form.span, usage)),
        }
    }

    /// A parameter's number, from 0, of a procedure of `n`.
    fn prop_param(&self, i: &Syntax, n: usize) -> R<usize> {
        match self.literal_int(i).filter(|i| *i >= 0 && (*i as usize) < n) {
            Some(k) => Ok(k as usize),
            None => Err(FxError::at(i.span, format!("a parameter's number, from 0 to {}", n as i64 - 1))),
        }
    }

    /// A size in a proposition: a parameter's number, `(length i)` or
    /// `(lit k)`.
    fn prop_term(&mut self, x: &Syntax, n: usize) -> R<crate::ast::Term> {
        use crate::ast::Term;
        if self.literal_int(x).is_some() {
            return Ok(Term::Param(self.prop_param(x, n)?));
        }
        let usage = "a size: a parameter's number, `(length i)`, or `(lit k)`";
        let parts = self.items(x, usage)?.to_vec();
        match &parts[..] {
            [h, i] if h.as_symbol().is_some_and(|h| self.name(h) == "length") => Ok(Term::Length(self.prop_param(i, n)?)),
            [h, k] if h.as_symbol().is_some_and(|h| self.name(h) == "lit") => match self.literal_int(k).filter(|k| *k >= 0) {
                Some(k) => Ok(Term::Lit(k)),
                None => Err(FxError::at(k.span, "a natural")),
            },
            _ => Err(FxError::at(x.span, usage)),
        }
    }

    /// A name for an expansion's own variable that `forms` never mention:
    /// `base`, else `base1`, `base2` and so on. The variable's scope is
    /// within the form, and nothing refers to a name it does not write, so
    /// it captures nothing and nothing captures it.
    fn fresh_name(&mut self, base: &str, forms: &[Syntax]) -> Sym {
        fn mentions(s: &Syntax, out: &mut std::collections::HashSet<Sym>) {
            match &s.datum {
                Datum::Symbol(x) => {
                    out.insert(*x);
                }
                Datum::List { items, tail } => {
                    items.iter().for_each(|i| mentions(i, out));
                    tail.iter().for_each(|t| mentions(t, out));
                }
                Datum::Vector(items) => items.iter().for_each(|i| mentions(i, out)),
                _ => {}
            }
        }
        let mut seen = std::collections::HashSet::new();
        forms.iter().for_each(|f| mentions(f, &mut seen));
        (0..)
            .map(|i| if i == 0 { base.to_string() } else { format!("{base}{i}") })
            .map(|n| self.interner.intern(&n))
            .find(|s| !seen.contains(s))
            .expect("a name")
    }

/// The fewest data a `case` searches by halving rather than in turn, by
/// kind: measured natively, register code (`TODO.md` §46). Characters never:
/// `char->integer` is a call-out, and every `char=?` a single instruction.
const CASE_TREE_INTS: usize = 8;
const CASE_TREE_STRINGS: usize = 16;
const CASE_TREE_SYMBOLS: usize = 32;
/// The same where the leaves give an index, which a second search takes to
/// a body: integers and symbols then pay only from more data.
const CASE_TREE_INTS_INDEXED: usize = 32;
const CASE_TREE_SYMBOLS_INDEXED: usize = 64;

    /// `(case key ((datum …) e …) … (else e …))` on atoms (`TODO.md` §46):
    /// `(let ((%case-key key)) …)` and a chain of `if`s, each datum compared
    /// by its kind's equality: `=` on integers, `char=?`, `string=?`,
    /// `symbol=?`, `bool=?`. The data are of one kind and distinct, and the
    /// `else` is required, as `cond`'s is.
    fn parse_case(&mut self, span: fixpt_read::Span, items: &[Syntax]) -> R<ExpId> {
        let usage = "`(case key ((datum …) expression …) … (else expression …))`";
        let [key, clauses @ ..] = items else {
            return Err(FxError::at(span, usage));
        };
        let Some((last, init)) = clauses.split_last() else {
            return Err(FxError::at(span, "a `case` needs at least an `else` clause"));
        };
        let parts = self.items(last, "a case clause")?.to_vec();
        if parts.first().and_then(|h| h.as_symbol()).map(|h| self.name(h)) != Some("else") {
            return Err(FxError::at(last.span, "a `case` must end with an `else` clause: FX has no unspecified value"));
        }
        // A variable, which nothing assigns, is compared as it is; any other
        // key is bound once.
        let key_span = key.span;
        let direct = key.as_symbol().filter(|s| !matches!(self.name(*s), "#t" | "#f" | "#u")).filter(|_| !init.is_empty());
        let (tmp, key) = match direct {
            Some(s) => (s, None),
            None => (self.fresh_name("%case-key", items), Some(self.parse_exp(key)?)),
        };
        let (mut kind, mut seen) = (None, std::collections::HashSet::new());
        let mut arms = Vec::new();
        // Each datum's test, the value a tree sorts it by (if it has one)
        // and its clause, for `case_tree`.
        let mut entries: Vec<(ExpId, Option<i64>, usize)> = Vec::new();
        for c in init {
            let parts = self.items(c, "a case clause")?.to_vec();
            let [data, body @ ..] = &parts[..] else {
                return Err(FxError::at(c.span, "a case clause is `((datum …) expression …)`"));
            };
            let data = self.items(data, "a case clause's data, `(datum …)`")?.to_vec();
            if data.is_empty() {
                return Err(FxError::at(c.span, "a case clause has at least one datum"));
            }
            let mut tests = Vec::new();
            for d in &data {
                let (k, eq, lit, text) = self.case_datum(d)?;
                if *kind.get_or_insert(k) != k {
                    return Err(FxError::at(d.span, "a `case`'s data are all of one kind: integers, characters, strings, symbols or booleans"));
                }
                if !seen.insert(text) {
                    return Err(FxError::at(d.span, "a datum appears twice in this `case`"));
                }
                let f = self.standard_ref_at(d.span, eq);
                let a = self.arena.exp(key_span, Exp::Var(tmp));
                let test = self.arena.exp(d.span, Exp::App { fun: f, args: vec![a, lit] });
                tests.push(test);
                entries.push((test, self.case_sort_key(k, d), arms.len()));
            }
            arms.push((c.span, tests, body.to_vec()));
        }
        // The bodies first to last, then the `else`'s, as the FX-26 parser.
        let mut thens = Vec::new();
        for (cspan, _, body) in &arms {
            thens.push(self.parse_body(*cspan, body)?);
        }
        let mut out = self.parse_body(last.span, &parts[1..])?;
        // A clause per datum and an `else` of one atom: each leaf gives its
        // body, the `else` made again at each, with no index to search.
        let atom_else = matches!(&parts[1..], [x] if !matches!(x.datum, Datum::List { .. } | Datum::Vector(_)));
        let direct = (atom_else && entries.len() == arms.len()).then(|| (last.span, parts[1].clone()));
        let tree_from = match (kind, direct.is_some()) {
            (Some(0), true) => Self::CASE_TREE_INTS,
            (Some(0), false) => Self::CASE_TREE_INTS_INDEXED,
            (Some(2), _) => Self::CASE_TREE_STRINGS,
            (Some(3), true) => Self::CASE_TREE_SYMBOLS,
            (Some(3), false) => Self::CASE_TREE_SYMBOLS_INDEXED,
            _ => usize::MAX,
        };
        if entries.len() >= tree_from && entries.iter().all(|e| e.1.is_some()) {
            let mut bodies = thens;
            bodies.push(out);
            let hash = match kind {
                Some(2) => Some("string-hash"),
                Some(3) => Some("symbol-name-hash"),
                _ => None,
            };
            let tree = self.case_tree(span, items, hash, key_span, tmp, entries, bodies, direct)?;
            return Ok(match key {
                Some(key) => self.arena.exp(span, Exp::Let { bindings: vec![(tmp, key)], body: tree }),
                None => tree,
            });
        }
        for ((cspan, tests, _), then) in arms.into_iter().zip(thens).rev() {
            let mut tests = tests.into_iter().rev();
            let mut test = tests.next().expect("a datum");
            for t in tests {
                let yes = self.arena.exp(cspan, Exp::Bool(true));
                test = self.arena.exp(cspan, Exp::If { test: t, then: yes, els: test });
            }
            out = self.arena.exp(cspan, Exp::If { test, then, els: out });
        }
        Ok(match key {
            Some(key) => self.arena.exp(span, Exp::Let { bindings: vec![(tmp, key)], body: out }),
            None => out,
        })
    }

    /// What a `case` tree sorts datum `d`, of kind `k`, by: an integer's
    /// value (a fixnum's), a string's or a symbol's hash, as the runtime
    /// computes them (`%string-hash`, `%symbol-hash`); none otherwise.
    fn case_sort_key(&self, k: u8, d: &Syntax) -> Option<i64> {
        match (k, &d.datum) {
            (0, Datum::Number(fixpt_read::Num::Int(n))) if (FIXNUM_MIN..=FIXNUM_MAX).contains(n) => Some(*n),
            (2, Datum::Str(t)) => Some(fixpt_heap::heap::string_hash_of(t)),
            (3, Datum::Symbol(x)) => Some(fixpt_heap::heap::symbol_hash_of(self.name(*x))),
            _ => None,
        }
    }

    /// A `case` of many data as two searches (`TODO.md` §46, Clinger's
    /// "Rapid Case Dispatch"): the clause's index found by halving the data
    /// sorted (by the integer, or by a hash of the key computed once), each
    /// leaf of three or fewer data their tests, in order; then the body by
    /// halving the indices, `bodies` the clauses' and the `else`'s last.
    #[allow(clippy::too_many_arguments)]
    fn case_tree(
        &mut self,
        span: fixpt_read::Span,
        items: &[Syntax],
        hash_op: Option<&str>,
        key_span: fixpt_read::Span,
        key: Sym,
        mut entries: Vec<(ExpId, Option<i64>, usize)>,
        bodies: Vec<ExpId>,
        direct: Option<(fixpt_read::Span, Syntax)>,
    ) -> R<ExpId> {
        entries.sort_by_key(|e| e.1);
        let m = bodies.len() - 1;
        let (hash, index) = (self.fresh_name("%case-hash", items), self.fresh_name("%case-index", items));
        let (by, by_span) = if hash_op.is_some() { (hash, span) } else { (key, key_span) };
        let tree = match &direct {
            Some(els) => {
                let leaves = CaseLeaves::Bodies(&bodies, els);
                self.case_index(span, by, by_span, &entries, m, &leaves)?
            }
            None => {
                let found = self.case_index(span, by, by_span, &entries, m, &CaseLeaves::Index)?;
                let chosen = self.case_bodies(span, index, &bodies, 0, m);
                self.arena.exp(span, Exp::Let { bindings: vec![(index, found)], body: chosen })
            }
        };
        let Some(op) = hash_op else { return Ok(tree) };
        let f = self.standard_ref_at(span, op);
        let k = self.arena.exp(key_span, Exp::Var(key));
        let h = self.arena.exp(span, Exp::App { fun: f, args: vec![k] });
        Ok(self.arena.exp(span, Exp::Let { bindings: vec![(hash, h)], body: tree }))
    }

    /// The clause index of `entries` (sorted, each its test and sort value),
    /// `m` for none: `by` (the key, or its hash) halved against the sort
    /// values; three or fewer, or all of one value, their tests in turn.
    fn case_index(
        &mut self,
        span: fixpt_read::Span,
        by: Sym,
        by_span: fixpt_read::Span,
        entries: &[(ExpId, Option<i64>, usize)],
        m: usize,
        leaves: &CaseLeaves,
    ) -> R<ExpId> {
        let n = entries.len();
        let key_of = |i: usize| entries[i].1.expect("sorted by a value");
        // A split between unequal values, nearest the middle.
        let mut mid = n / 2;
        while mid < n && mid > 0 && key_of(mid) == key_of(mid - 1) {
            mid += 1;
        }
        if mid == n {
            mid = n / 2;
            while mid > 0 && key_of(mid) == key_of(mid - 1) {
                mid -= 1;
            }
        }
        if n <= 3 || mid == 0 {
            let mut out = match leaves {
                CaseLeaves::Index => self.arena.exp(span, Exp::Int(m as i64)),
                CaseLeaves::Bodies(_, (els_span, els)) => self.parse_body(*els_span, std::slice::from_ref(els))?,
            };
            for (test, _, c) in entries.iter().rev() {
                let then = match leaves {
                    CaseLeaves::Index => self.arena.exp(span, Exp::Int(*c as i64)),
                    CaseLeaves::Bodies(bodies, _) => bodies[*c],
                };
                out = self.arena.exp(span, Exp::If { test: *test, then, els: out });
            }
            return Ok(out);
        }
        let less = self.standard_ref_at(span, "<");
        let v = self.arena.exp(by_span, Exp::Var(by));
        let pivot = self.arena.exp(span, Exp::Int(key_of(mid)));
        let test = self.arena.exp(span, Exp::App { fun: less, args: vec![v, pivot] });
        let then = self.case_index(span, by, by_span, &entries[..mid], m, leaves)?;
        let els = self.case_index(span, by, by_span, &entries[mid..], m, leaves)?;
        Ok(self.arena.exp(span, Exp::If { test, then, els }))
    }

    /// The body of index `lo`..=`hi` that `index` names, by halving.
    fn case_bodies(&mut self, span: fixpt_read::Span, index: Sym, bodies: &[ExpId], lo: usize, hi: usize) -> ExpId {
        if lo == hi {
            return bodies[lo];
        }
        let mid = (lo + hi).div_ceil(2);
        let less = self.standard_ref_at(span, "<");
        let i = self.arena.exp(span, Exp::Var(index));
        let pivot = self.arena.exp(span, Exp::Int(mid as i64));
        let test = self.arena.exp(span, Exp::App { fun: less, args: vec![i, pivot] });
        let then = self.case_bodies(span, index, bodies, lo, mid - 1);
        let els = self.case_bodies(span, index, bodies, mid, hi);
        self.arena.exp(span, Exp::If { test, then, els })
    }

    /// A `case` datum: its kind, its kind's equality, its literal, and a
    /// text that tells it from the others.
    fn case_datum(&mut self, d: &Syntax) -> R<(u8, &'static str, ExpId, String)> {
        let bad = "a `case` datum is an integer, a character, a string, a symbol or a boolean";
        let (kind, eq, text) = match &d.datum {
            Datum::Number(fixpt_read::Num::Int(n)) => (0, "=", format!("{n}")),
            Datum::Number(fixpt_read::Num::Big { negative, digits, radix }) => {
                (0, "=", format!("{negative}:{radix}:{}", digits.trim_start_matches('0')))
            }
            Datum::Char(c) => (1, "char=?", format!("{c}")),
            Datum::Str(t) => (2, "string=?", t.clone()),
            Datum::Bool(b) => (4, "bool=?", format!("{b}")),
            Datum::Symbol(sym) => match self.name(*sym) {
                "#t" => (4, "bool=?", "true".to_string()),
                "#f" => (4, "bool=?", "false".to_string()),
                "#u" => return Err(FxError::at(d.span, bad)),
                n => {
                    let text = n.to_string();
                    let lit = self.arena.exp(d.span, Exp::Symbol(*sym));
                    return Ok((3, "symbol=?", lit, text));
                }
            },
            _ => return Err(FxError::at(d.span, bad)),
        };
        Ok((kind, eq, self.parse_exp(d)?, text))
    }

    /// A label or tag: a symbol, or a positive integer, as FX-91's
    /// `define-datatype` numbers a variant's members.
    /// A procedure type's parameter written `(name type)`: its name and
    /// type, where `name` names no type or type form.
    pub(crate) fn named_param(&self, p: &Syntax) -> Option<(Sym, Syntax)> {
        let [n, colon, t] = p.as_proper_list()? else { return None };
        (colon.as_symbol().map(|c| self.name(c)) == Some(":")).then_some(())?;
        Some((n.as_symbol()?, t.clone()))
    }

    /// `(h t)`, parameter `p`, is `h` applied; refused, saying how to name
    /// a parameter, where `h` is no description function: where `later`
    /// (the parameters after it, the result, the specification's clauses)
    /// names `h`, as `(select h x)` or a proposition does; or where `h` is
    /// unknown and no module included or opened by `with` may give it.
    fn misnamed_param(&self, p: &Syntax, later: &[&Syntax]) -> R<()> {
        let Some([h, _]) = p.as_proper_list() else { return Ok(()) };
        let Some(h) = h.as_symbol() else { return Ok(()) };
        let name = self.name(h);
        if TYPE_FORMS.contains(&name) || crate::top::KEYWORDS.contains(&name) || self.lookup_desc(h).is_some() || self.base.contains_key(&h) {
            return Ok(());
        }
        let fix = format!("to name a parameter, write `({name} : type)`");
        if let Some(used) = later.iter().find_map(|s| self.named_in(s, h)) {
            let what = if used.is_empty() { "what follows".to_string() } else { format!("`{used}` after it") };
            return Err(FxError::at(p.span, format!("`({name} …)` applies `{name}`, but {what} names `{name}`: {fix}")));
        }
        if self.include_scope == 0 && self.withs_over(h).is_empty() {
            return Err(FxError::at(p.span, format!("`{name}` is not a description function: {fix}")));
        }
        Ok(())
    }

    /// Where `s` has `n` other than as a list's head: the list it is in,
    /// shown if all of it is names, else "".
    fn named_in(&self, s: &Syntax, n: Sym) -> Option<String> {
        let items = s.as_proper_list()?;
        let skip = usize::from(items.first().is_some_and(|x| x.as_symbol().is_some()));
        if items[skip..].iter().any(|x| x.as_symbol() == Some(n)) {
            let names: Option<Vec<&str>> = items.iter().map(|x| x.as_symbol().map(|y| self.name(y))).collect();
            return Some(names.map_or(String::new(), |ns| format!("({})", ns.join(" "))));
        }
        items.iter().find_map(|x| self.named_in(x, n))
    }

    /// `t` with each `(select m x)` of a parameter named before it, the
    /// `k`th, made `(select $k x)`.
    fn select_params(&mut self, t: TyId, names: &[Option<Sym>]) -> TyId {
        if names.iter().all(|n| n.is_none()) {
            return t;
        }
        let mut found = Vec::new();
        self.selects_in(t, &mut std::collections::HashSet::new(), &mut found);
        let mut sel = std::collections::HashMap::new();
        for (m, x, _) in found {
            if let Some(k) = names.iter().rposition(|n| *n == Some(m)) {
                sel.insert((m, x), self.arena.ty(Ty::ParamSel(k, x)));
            }
        }
        if sel.is_empty() {
            return t;
        }
        let outer = std::mem::replace(&mut self.select_map, sel);
        let r = self.subst(t, &std::collections::HashMap::new());
        self.select_map = outer;
        r
    }

    /// A `moduleof`'s components (`docs/research/first-class-modules.md`):
    /// `(abs t type)` or `(abs (t …) type)`, `(desc d T)`, `(val x T)`, each
    /// name once; the abstract types in scope in what follows them.
    fn parse_moduleof(&mut self, span: fixpt_read::Span, comps: &[Syntax]) -> R<TyId> {
        let depth = self.dscope.len();
        let r = self.parse_moduleof_in(span, comps);
        self.dscope.truncate(depth);
        r
    }

    /// `(abs (f (a kind) …) type)`'s name and its parameters' kinds, unread:
    /// `(abs f (=> (kind …) type))`, as `define-generative` writes its
    /// parameters.
    fn abs_ctor(&mut self, name: &Syntax, ns: &[Syntax]) -> R<(Sym, Vec<Syntax>)> {
        let err = || FxError::at(name.span, ABS_CTOR_USAGE);
        let Some(f) = ns[0].as_symbol() else { return Err(err()) };
        let mut ks = Vec::new();
        for p in &ns[1..] {
            match p.as_proper_list() {
                Some([n, k]) if n.as_symbol().is_some() => ks.push(k.clone()),
                _ => return Err(err()),
            }
        }
        Ok((f, ks))
    }

    fn parse_moduleof_in(&mut self, span: fixpt_read::Span, comps: &[Syntax]) -> R<TyId> {
        let usage = "`(moduleof (abs t type) … (desc d type) … (val x type) …)`";
        let (mut abs, mut descs, mut vals): (Vec<(Sym, DVar)>, Vec<(Sym, TyId)>, Vec<(Sym, TyId)>) = (Vec::new(), Vec::new(), Vec::new());
        // Names given twice: as descriptions, or as values (a value may have
        // a type's name).
        let (mut seen, mut vseen): (Vec<Sym>, Vec<Sym>) = (Vec::new(), Vec::new());
        for c in comps {
            let parts = self.items(c, "a module component")?.to_vec();
            let [head, name, what] = &parts[..] else {
                return Err(FxError::at(c.span, usage));
            };
            // `(abs (t …) type)` names several; `(abs (f (a kind) …) type)`
            // is one constructor, its parameters' kinds given.
            let mut ctor: Option<Vec<Syntax>> = None;
            let names: Vec<Sym> = match (name.as_symbol(), name.as_proper_list()) {
                (Some(n), _) => vec![n],
                (None, Some(ns)) if self.head(&parts) == Some("abs") && ns.iter().all(|n| n.as_symbol().is_some()) => {
                    ns.iter().filter_map(|n| n.as_symbol()).collect()
                }
                (None, Some(ns)) if self.head(&parts) == Some("abs") => {
                    let (f, ks) = self.abs_ctor(name, ns)?;
                    ctor = Some(ks);
                    vec![f]
                }
                _ => return Err(FxError::at(name.span, "a component's name")),
            };
            let seen = if self.head(&parts) == Some("val") { &mut vseen } else { &mut seen };
            for n in &names {
                if seen.contains(n) {
                    return Err(FxError::at(c.span, format!("`{}` appears twice", self.name(*n))));
                }
                seen.push(*n);
            }
            match self.head(&parts) {
                Some("abs") => {
                    // A type, or a type constructor: a description function
                    // to a type (`crate::kinds`).
                    let ks = match ctor.take() {
                        Some(ks) if what.as_symbol().map(|k| self.name(k)) == Some("type") => {
                            let ks = ks.iter().map(|k| self.parse_kind(k)).collect::<R<Vec<_>>>();
                            Some(ks.map_err(|_| FxError::at(name.span, ABS_CTOR_USAGE))?)
                        }
                        Some(_) => return Err(FxError::at(name.span, ABS_CTOR_USAGE)),
                        None => None,
                    };
                    let kind = match what.as_symbol().map(|k| self.name(k)) {
                        _ if ks.is_some() => self.arena.arrow(ks.unwrap_or_default(), Kind::Type),
                        Some("type") => Kind::Type,
                        _ => match self.parse_kind(what) {
                            Ok(k) if self.arena.arrow_parts(k).is_some_and(|(_, r)| r == Kind::Type) => k,
                            _ => return Err(FxError::at(what.span, "an abstract component is a `type`, or a type constructor `(=> (kind …) type)`, for now")),
                        },
                    };
                    for n in names {
                        let v = self.arena.dvar_of(n, kind);
                        if kind != Kind::Type {
                            self.abstract_funs.insert(v);
                        }
                        self.dscope.push((n, DScope::Var(v, kind)));
                        abs.push((n, v));
                    }
                }
                // `(desc e E)`, an effect, as a module's `define-effect` gives.
                Some("desc") if self.effect_shaped(what) => {
                    let e = self.parse_effect(what)?;
                    self.dscope.push((names[0], DScope::Eff(e.clone())));
                    let d = self.effect_desc(e);
                    descs.push((names[0], d));
                }
                Some("desc") if self.head(&self.items(what, "").unwrap_or(&[]).to_vec()) == Some("dlambda") => {
                    let f = self.parse_fun(what, None)?;
                    self.dscope.push((names[0], DScope::Fun(f)));
                    descs.push((names[0], f));
                }
                Some("desc") => {
                    let t = self.parse_type(what)?;
                    self.dscope.push((names[0], DScope::Rec(t)));
                    descs.push((names[0], t));
                }
                Some("val") => vals.push((names[0], self.parse_type(what)?)),
                _ => return Err(FxError::at(head.span, usage)),
            }
        }
        let _ = span;
        Ok(self.arena.ty(Ty::Module { abs, descs, vals }))
    }

    /// `(load-module "path")` or, `input`, `(load-input "path")`: every
    /// load of a path is one value, made once (`TODO.md` §68). A load is its
    /// key, the path resolved (`input:` before it, for a `load-input`), as
    /// Sheldon's `(input "file")` is the file it names; its value the hidden
    /// global `%shared:key`, which the first defines, `(define %shared:key
    /// (%loaded "key" "path"))`, checked so, alone, its definition running
    /// before the form that loads it (`hoisted`). Making it must be pure: a
    /// file's state is made by applying what it makes, so that two loads
    /// that are one cannot be told apart.
    ///
    /// What it makes is the form's, at its span; the file's module, the
    /// whole file's.
    pub(crate) fn parse_load(&mut self, span: fixpt_read::Span, path: &str, input: bool) -> R<ExpId> {
        let at = match &self.base_dir {
            Some(d) if std::path::Path::new(path).is_relative() && crate::built_in_module(path).is_none() => d.join(path),
            _ => std::path::PathBuf::from(path),
        };
        // A file of module parameters is read as a `load-input` file is, its
        // value the function of them it makes (`modules_made`).
        let written_input = input;
        let input = input || takes_modules_at(&at, path);
        let key = format!("{}{}", if input { "input:" } else { "" }, at.display());
        // A file loading one that is being read, itself or one that loads
        // it: a cycle, refused, the chain named (`TODO.md` §71). As the
        // FX-26 parser's `parse-loaded`.
        if let Some(i) = self.loading.iter().position(|(k, _)| *k == key) {
            let chain: Vec<String> = self.loading[i..].iter().map(|(_, p)| format!("`{p}`")).chain([format!("`{path}`")]).collect();
            return Err(FxError::at(span, format!("a load cycle: {}", chain.join(" loads "))));
        }
        let name = match self.shared_loads.get(&key) {
            Some(n) => *n,
            None => {
                let name = self.interner.intern(&format!("%shared:{key}"));
                let sym = |c: &mut Self, s: &str| Syntax::symbol(span, c.interner.intern(s));
                let str = |s: &str| Syntax::new(span, Datum::Str(s.to_string()));
                let loaded = Syntax::list(span, vec![sym(self, "%loaded"), str(&key), str(path)]);
                let form = Syntax::list(span, vec![sym(self, "define"), Syntax::symbol(span, name), loaded]);
                let made = self.top_defining(&form)?;
                for (top, _) in &made.run {
                    // Pure but for reading globals: the hidden globals of the
                    // files it loads, which never change.
                    if let crate::top::Top::Define { effect, .. } = top
                        && !effect.0.iter().all(|a| matches!(a, crate::ast::Atom::Read(r) if r.is_globals()))
                    {
                        return Err(FxError::at(
                            span,
                            format!(
                                "a loaded file is one value for all its loads, made once, so making it must be pure, and this one has {}\n  a file whose definitions make state as it is made is a program's: run it with `,load FILE` or `fixpt run`; or, a module, give its state in a `lambda` it gives, which each caller applies",
                                self.show_effect(effect)
                            ),
                        ));
                    }
                }
                // The type its load is checked at, for a `.fasl` of it.
                if let Some((crate::top::Top::Define { ty, .. }, _)) = made.run.first()
                    && let Some(f) = self.shared_files.get_mut(&name)
                {
                    f.ty = Some(*ty);
                }
                self.hoisted.extend(made.hoisted);
                self.hoisted.extend(made.run);
                self.shared_loads.insert(key, name);
                self.shared_globals.insert(name);
                name
            }
        };
        // One of the loads of the file being read, if one is: a `.fasl`'s.
        if let Some(deps) = self.reading_deps.last_mut()
            && !deps.iter().any(|(_, _, n)| *n == name)
        {
            deps.push((path.to_string(), written_input, name));
        }
        let var = self.arena.exp(span, Exp::Var(name));
        if !input {
            return Ok(var);
        }
        // A `load-input`'s value: its module's one item, `input`.
        let item = self.interner.intern("input");
        let body = self.arena.exp(span, Exp::Var(item));
        Ok(self.arena.exp(span, Exp::With { module: name, body }))
    }

    /// `(restrict T name …)`, `items`: module type `T` with only the values,
    /// types and effects named. It drops names, not types: a description
    /// not named is spelt out where a type kept uses it; an abstract type
    /// not named that a type kept mentions stays, unnamed, `%hidden:t`,
    /// so a module of `T` fits it (`bare_name`), and a client may pass its
    /// values but not name its type. `T` must be known as a module's type
    /// where it is read: a `define-type` of one is read in order.
    fn restricted(&mut self, s: &Syntax, items: &[Syntax]) -> R<TyId> {
        let [_, t, names @ ..] = items else {
            return Err(FxError::at(s.span, "`(restrict module-type name …)`"));
        };
        let t = self.parse_type(t)?;
        let Ty::Module { abs, descs, vals } = self.arena.get(self.arena.resolve(t)).clone() else {
            return Err(FxError::at(s.span, format!("`restrict` restricts a module's type, and this is a {}", self.show_ty(t))));
        };
        let mut kept = Vec::new();
        for n in names {
            let Some(name) = n.as_symbol() else { return Err(FxError::at(n.span, "`restrict` keeps names")) };
            let has = |ps: &[(Sym, TyId)]| ps.iter().any(|(m, _)| *m == name);
            if !(abs.iter().any(|(m, _)| *m == name) || has(&descs) || has(&vals)) {
                return Err(FxError::at(n.span, format!("the module gives no `{}`", self.name(name))));
            }
            kept.push(name);
        }
        let descs: Vec<(Sym, TyId)> = descs.into_iter().filter(|(n, _)| kept.contains(n)).collect();
        let vals: Vec<(Sym, TyId)> = vals.into_iter().filter(|(n, _)| kept.contains(n)).collect();
        let mut out = Vec::new();
        for (n, v) in abs {
            if kept.contains(&n) {
                out.push((n, v));
            } else if descs.iter().chain(&vals).any(|(_, t)| self.mentions_var(*t, v)) {
                let hidden = format!("%hidden:{}", self.name(n));
                out.push((self.interner.intern(&hidden), v));
            }
        }
        Ok(self.arena.ty(Ty::Module { abs: out, descs, vals }))
    }

    /// The hidden global a load of `path` is (`parse_load`).
    pub(crate) fn load_name(&mut self, span: fixpt_read::Span, path: &str, input: bool) -> R<Sym> {
        let e = self.parse_load(span, path, input)?;
        match *self.arena.exp_at(e) {
            Exp::Var(n) | Exp::With { module: n, .. } => Ok(n),
            _ => unreachable!("a load is its hidden global"),
        }
    }

    /// The type of value `name` of module type `t`, if it gives one.
    fn module_val(&self, t: TyId, name: &str) -> Option<TyId> {
        match self.arena.get(self.arena.resolve(t)) {
            Ty::Module { vals, .. } => vals.iter().find(|(n, _)| self.name(*n) == name).map(|(_, t)| *t),
            _ => None,
        }
    }

    /// What a value of type `t`, the file `path` loaded, makes given
    /// `args` (`load-moduleof`): a `poly` takes as many descriptions as it
    /// binds, as `proj` does; a procedure of no parameters is applied; a
    /// procedure's parameters take one argument each, a module's name
    /// where the types after it select from it, as a call does (M5), its
    /// types those of that module. Done when the arguments are, and no
    /// procedure of no parameters is left: a module's type, or refused.
    fn type_made(&mut self, mut t: TyId, mut args: &[Syntax], span: fixpt_read::Span, path: &str) -> R<TyId> {
        loop {
            match self.arena.get(self.arena.resolve(t)).clone() {
                Ty::Poly { binders, body } if !args.is_empty() => {
                    let Some((now, rest)) = args.split_at_checked(binders.len()) else {
                        return Err(FxError::at(span, format!("`{path}` makes a `poly` of {} description(s), and {} are given", binders.len(), args.len())));
                    };
                    let mut map = std::collections::HashMap::new();
                    for ((v, k), a) in binders.iter().zip(now) {
                        let d = self.parse_d(a)?;
                        if !self.d_fits(&d, *k) {
                            let word = self.kind_word(*k);
                            return Err(FxError::at(a.span, format!("`{}` is bound as a {word}, and the description given is not one", self.name(self.arena.dvar_name(*v)))));
                        }
                        map.insert(*v, d);
                    }
                    t = self.subst(body, &map);
                    args = rest;
                }
                Ty::Subr { params, result, .. } if params.is_empty() => t = result,
                Ty::Subr { params, result, .. } if !args.is_empty() => {
                    let Some((now, rest)) = args.split_at_checked(params.len()) else {
                        return Err(FxError::at(span, format!("`{path}` makes a procedure of {} parameter(s), and {} are given", params.len(), args.len())));
                    };
                    let mut found = Vec::new();
                    self.param_sels(result, &mut std::collections::HashSet::new(), &mut found);
                    let mut map = std::collections::HashMap::new();
                    for (k, x) in found {
                        let Some(m) = now[k].as_symbol() else {
                            return Err(FxError::at(now[k].span, format!("argument {} is a module the types `{path}` makes depend on: give it by name", k + 1)));
                        };
                        map.insert((k, x), self.arena.ty(Ty::Select(m, x)));
                    }
                    t = self.instantiate_params(result, &map);
                    args = rest;
                }
                Ty::Module { .. } if args.is_empty() => return Ok(t),
                _ if args.is_empty() => {
                    return Err(FxError::at(span, format!("what `{path}` makes, given these, is a {}, not a module", self.show_ty(t))));
                }
                _ => return Err(FxError::at(span, format!("what `{path}` makes is a {}, given no more", self.show_ty(t)))),
            }
        }
    }

    /// Each `(load-moduleof "file" …)` and `(load-input-moduleof "file" …)`
    /// in form `s`, outside quotations, loaded as a load of the file is, in
    /// order: before the loads of its expressions, as the FX-26 parser
    /// takes them (`type-loaded`) and the driver reads them for it
    /// (`syn::load_modules_in`).
    pub(crate) fn type_loads(&mut self, s: &Syntax) -> R<()> {
        let Some(items) = s.as_proper_list() else { return Ok(()) };
        match items.first().and_then(|h| h.as_symbol()).map(|h| self.name(h)) {
            Some("quote" | "quasiquote") => Ok(()),
            Some(loader @ ("load-moduleof" | "load-input-moduleof")) => {
                let input = loader == "load-input-moduleof";
                if let Some(Datum::Str(path)) = items.get(1).map(|p| &p.datum) {
                    let path = path.clone();
                    self.parse_load(s.span, &path, input)?;
                }
                Ok(())
            }
            _ => items.iter().try_for_each(|x| self.type_loads(x)),
        }
    }

    /// `(%loaded "key" "path")`: the module of the file `key` names (the
    /// path resolved, `input:` before it for a file of one expression,
    /// whose module's one item is `input`), wherever it is read; `path` as
    /// the load wrote it, for what is said of the file.
    fn parse_loaded(&mut self, span: fixpt_read::Span, key: &str, path: &str) -> R<ExpId> {
        let (input, file) = match key.strip_prefix("input:") {
            Some(f) => (true, f),
            None => (false, key),
        };
        // A file loading one that is being read: a cycle, as `parse_load`
        // refuses it.
        if let Some(i) = self.loading.iter().position(|(k, _)| k == key) {
            let chain: Vec<String> = self.loading[i..].iter().map(|(_, p)| format!("`{p}`")).chain([format!("`{path}`")]).collect();
            return Err(FxError::at(span, format!("a load cycle: {}", chain.join(" loads "))));
        }
        self.loading.push((key.to_string(), path.to_string()));
        let r = self.parse_load_kept(span, key, path, std::path::Path::new(file), input);
        self.loading.pop();
        r
    }

    /// The file at `at`, `path` as written, for its load (key `key`): read
    /// from its `.fasl`, if a driver reads them and it is fresh
    /// ([`fasl_load`](Self::fasl_load)); else read and parsed
    /// ([`parse_load_file`](Self::parse_load_file)). Either way kept for a
    /// `.fasl` of it (`shared_files`): its digest, stamp and loads.
    fn parse_load_kept(&mut self, span: fixpt_read::Span, key: &str, path: &str, at: &std::path::Path, input: bool) -> R<ExpId> {
        let text = match crate::built_in_module(path) {
            Some(t) => t.to_string(),
            None => std::fs::read_to_string(at).map_err(|e| FxError::at(span, format!("cannot read `{path}`: {e}")))?,
        };
        let source = crate::fasl::digest(&text);
        let name = self.interner.intern(&format!("%shared:{key}"));
        if self.fasls
            && crate::built_in_module(path).is_none()
            && let Some(e) = self.fasl_load(span, key, path, at, input, source)?
        {
            return Ok(e);
        }
        self.reading_deps.push(Vec::new());
        let r = self.parse_load_file(span, path, at, input, text);
        let deps = self.reading_deps.pop().unwrap_or_default();
        let stamps: Vec<u64> = deps.iter().map(|(_, _, n)| self.shared_files.get(n).map_or(0, |f| f.stamp)).collect();
        let stamp = crate::fasl::stamp(source, &stamps);
        let file = crate::fasl::SharedFile { key: key.to_string(), path: at.to_path_buf(), input, source, stamp, deps, ty: None, fasl: None };
        self.shared_files.insert(name, file);
        r
    }

    /// The file at `at`, `path` as written, its text `text`, parsed: its
    /// forms a module's items; or, `input`, its one form an expression, the
    /// one item, `input`, of the module made.
    fn parse_load_file(&mut self, span: fixpt_read::Span, path: &str, at: &std::path::Path, input: bool, text: String) -> R<ExpId> {
        self.files_read += 1;
        let file = fixpt_read::FileId(self.files_read + 1000);
        self.load_sites.insert(file, (span, path.to_string(), text.as_str().into()));
        let at_file = |e: FxError, c: &Self| c.in_loaded(e, file);
        let forms = match self.read_module_file(file, &text) {
            Ok(f) => f,
            Err(e) => return Err(at_file(e, self)),
        };
        let (depth, standard) = (self.dscope.len(), self.standard_dscope);
        let outer = self.hidden.replace(((0, 0), (standard, depth)));
        // Its own `load-module`s are from its directory.
        let outer_dir = std::mem::replace(&mut self.base_dir, at.parent().map(|d| d.to_path_buf()));
        let lives = self.lifetimes.len();
        let made = if input { self.modules_made(&forms) } else { None };
        let r = if input {
            match &forms[..] {
                _ if made.is_some() => {
                    let one = made.expect("made");
                    let item = Syntax::list(
                        one.span,
                        vec![Syntax::symbol(span, self.interner.intern("define")), Syntax::symbol(span, self.interner.intern("input")), one],
                    );
                    self.parse_module_in(&[item]).map(|items| (None, items))
                }
                [one] => {
                    let item = Syntax::list(
                        one.span,
                        vec![Syntax::symbol(span, self.interner.intern("define")), Syntax::symbol(span, self.interner.intern("input")), one.clone()],
                    );
                    self.parse_module_in(&[item]).map(|items| (None, items))
                }
                _ => Err(FxError::at(span, "a `load-input` file is one expression")),
            }
        } else {
            self.module_parameters(&forms).and_then(|(params, rest)| Ok((params, self.parse_module_in(rest)?)))
        };
        self.base_dir = outer_dir;
        self.dscope.truncate(depth);
        self.lifetimes.truncate(lives);
        self.hidden = outer;
        let (params, items) = r.map_err(|e| at_file(e, self))?;
        // At the whole file: no other expression is there.
        let whole = fixpt_read::Span::new(file, 0, text.len() as u32);
        self.defined_twice(whole, &items).map_err(|e| at_file(e, self))?;
        let e = self.arena.exp(whole, Exp::Module(items));
        self.loaded.insert(e, (path.to_string(), text.clone(), file));
        // A file of parameters, `(module-parameters ((name kind) …))` first:
        // a `plambda` over them of a `lambda` of none making the module, so
        // that whoever loads it gives them, and each call makes one; both at
        // the `module-parameters` form.
        Ok(match params {
            None => e,
            // `(module-parameters ())`, a module of state made once by a
            // `lambda` of none: no `plambda` of none around it (Heist's).
            Some(binders) if binders.is_empty() => self.arena.exp(forms[0].span, Exp::Lambda { params: Vec::new(), body: e }),
            Some(binders) => {
                let p = forms[0].span;
                let made = self.arena.exp(p, Exp::Lambda { params: Vec::new(), body: e });
                self.arena.exp(p, Exp::PLambda { binders, body: made })
            }
        })
    }

    /// A file of module parameters' one expression (Heist's, 2026-10-28):
    /// `(module-parameters ((name kind) … (m T) …))` first, `m` a module of
    /// type `T`, then the module's items, is
    ///
    /// ```text
    /// (plambda ((name kind) …) (lambda ((m T) …) (module (hide (include m) …) item …)))
    /// ```
    ///
    /// each module's values the items', hidden; no `plambda` with no kinds.
    /// None if the file has no module parameters.
    pub(crate) fn modules_made(&mut self, forms: &[Syntax]) -> Option<Syntax> {
        let (first, rest) = forms.split_first()?;
        let binders = module_parameters_of(first, &self.interner)?;
        let (kinds, modules): (Vec<Syntax>, Vec<Syntax>) = binders.iter().cloned().partition(|b| binder_is_kind(b, &self.interner));
        if modules.is_empty() {
            return None;
        }
        let at = first.span;
        let sym = |c: &mut Self, s: &str| Syntax::symbol(at, c.interner.intern(s));
        // Each included but those marked `qualified`; each a `lambda`'s
        // parameter, `(m T)`.
        let included: Vec<&Syntax> = modules.iter().filter(|b| !matches!(b.as_proper_list(), Some([_, _, q]) if is_qualified(q, &self.interner))).collect();
        let includes: Vec<Syntax> = included
            .into_iter()
            .map(|b| {
                let m = b.as_proper_list().expect("a binder")[0].clone();
                Syntax::list(m.span, vec![sym(self, "include"), m])
            })
            .collect();
        let modules: Vec<Syntax> = modules.iter().map(|b| Syntax::list(b.span, b.as_proper_list().expect("a binder")[..2].to_vec())).collect();
        let hide = Syntax::list(at, std::iter::once(sym(self, "hide")).chain(includes).collect());
        let module = Syntax::list(at, [sym(self, "module"), hide].into_iter().chain(rest.iter().cloned()).collect());
        let lambda = Syntax::list(at, vec![sym(self, "lambda"), Syntax::list(at, modules), module]);
        Some(match kinds.is_empty() {
            true => lambda,
            false => Syntax::list(at, vec![sym(self, "plambda"), Syntax::list(at, kinds), lambda]),
        })
    }

    /// A module's file's parameters, if its first form is
    /// `(module-parameters ((name kind) …))`, bound for the rest of it as a
    /// `plambda`'s are; and its other forms.
    fn module_parameters<'f>(&mut self, forms: &'f [Syntax]) -> R<(Option<Vec<(DVar, Kind)>>, &'f [Syntax])> {
        let Some((first, rest)) = forms.split_first() else { return Ok((None, forms)) };
        let Some(items) = first.as_proper_list() else { return Ok((None, forms)) };
        if !items.first().and_then(|h| h.as_symbol()).is_some_and(|h| self.name(h) == "module-parameters") {
            return Ok((None, forms));
        }
        let [_, binders] = items else {
            return Err(FxError::at(first.span, "`(module-parameters ((name kind) …))`"));
        };
        let lives = self.lifetimes.len();
        let binders = self.parse_binders(binders)?;
        for (v, k) in &binders {
            if matches!(k, Kind::Region | Kind::Place) {
                self.arena.set_outer(*v, self.lifetimes[..lives].to_vec());
                self.lifetimes.push(*v);
            }
        }
        Ok((Some(binders), rest))
    }

    /// An error in a module's file, said at the `load-module` that reads it,
    /// with where in the file; and so on out, a file loaded by a file loaded
    /// saying each on the way (`TODO.md` §73), whether or not the files
    /// between are being read or checked now (a load is made once, at the
    /// program's top).
    pub(crate) fn in_loaded(&self, mut e: FxError, file: fixpt_read::FileId) -> FxError {
        if e.span.file != file {
            return e;
        }
        while let Some((at, path, text)) = self.load_sites.get(&e.span.file) {
            e = Self::said_in(e, *at, path, text);
        }
        e
    }

    /// Error `e`, in the file of `path` and `text`, said where `span`
    /// starts (the load's start: all the FX-26 parser keeps of it).
    fn said_in(e: FxError, span: fixpt_read::Span, path: &str, text: &str) -> FxError {
        let before = &text[..(e.span.start as usize).min(text.len())];
        let line = before.matches('\n').count() + 1;
        let col = before.chars().rev().take_while(|c| *c != '\n').count() + 1;
        FxError::at(fixpt_read::Span::new(span.file, span.start, span.start), format!("in `{path}`, {line}:{col}: {}", e.message))
    }

    /// A `module`'s items, in order, each seeing those before it:
    /// `(define-generative t T)`, `(define-type d T)`, `(define x e)`,
    /// `(define x T e)` and `(define-rec (f T e) …)`.
    fn parse_module(&mut self, span: fixpt_read::Span, forms: &[Syntax]) -> R<ExpId> {
        // Its `define-datatype`s expanded, as a program's and a module
        // file's are (`expand_datatype`).
        let mut expanded = Vec::new();
        for f in forms {
            self.expand_datatype(f.clone(), &mut expanded)?;
        }
        let forms = &expanded[..];
        let depth = self.dscope.len();
        let r = self.parse_module_in(forms);
        self.dscope.truncate(depth);
        let items = r?;
        self.defined_twice(span, &items)?;
        Ok(self.arena.exp(span, Exp::Module(items)))
    }

    /// A module that defines a name twice is refused: it has no type
    /// (`moduleof` refuses a name twice), and which of the two a use got
    /// would depend on the path that ran it (one the first, another the
    /// last). Twice as a description, or twice as a value: a value may have
    /// a type's name. A generative type's conversions, `up-t` and `down-t`,
    /// count as values. As the FX-26 checker's `k-defined-twice`.
    fn defined_twice(&self, span: fixpt_read::Span, items: &[ModItem]) -> R<()> {
        let (mut types, mut values): (Vec<Sym>, Vec<Sym>) = (Vec::new(), Vec::new());
        for item in items {
            let (ts, vs): (Vec<Sym>, Vec<Sym>) = match item {
                ModItem::Abs { name, up, down, .. } => (vec![*name], vec![*up, *down]),
                ModItem::Desc { name, .. } => (vec![*name], vec![]),
                ModItem::Val { name, .. } => (vec![], vec![*name]),
                ModItem::Rec(bs) => (vec![], bs.iter().map(|(n, _, _)| *n).collect()),
            };
            let twice = ts.iter().find(|n| types.contains(n)).or_else(|| vs.iter().find(|n| values.contains(n)));
            if let Some(n) = twice {
                return Err(FxError::at(span, format!("`{}` is defined twice in this module", self.name(*n))));
            }
            types.extend(ts);
            values.extend(vs);
        }
        Ok(())
    }

    /// A module's items. Its type abbreviations are declared ahead, as a
    /// program's are (`declare_ahead`): each defined once, by name, in
    /// scope before any is read, so that they may name each other, and
    /// themselves, in any order; each checked grounded once all are.
    fn parse_module_in(&mut self, forms: &[Syntax]) -> R<Vec<ModItem>> {
        let outer = (std::mem::take(&mut self.ahead), std::mem::take(&mut self.ahead_filled));
        let mut names: Vec<Sym> = Vec::new();
        let mut twice: Vec<Sym> = Vec::new();
        for f in forms {
            let items = f.as_proper_list().unwrap_or(&[]);
            if let [h, n, d] = items
                && h.as_symbol().is_some_and(|h| self.name(h) == "define-type")
                && let Some(n) = n.as_symbol()
                && self.head(d.as_proper_list().unwrap_or(&[])) != Some("dlambda")
            {
                if names.contains(&n) { twice.push(n) } else { names.push(n) }
            }
        }
        for n in names.into_iter().filter(|n| !twice.contains(n)) {
            let slot = self.arena.ty(Ty::Link(None));
            self.dscope.push((n, DScope::Rec(slot)));
            self.ahead.push((n, slot));
        }
        let r = self.parse_module_items(forms).and_then(|out| {
            for (slot, span) in std::mem::take(&mut self.ahead_filled) {
                self.grounded(slot, span)?;
                self.note_closed(slot);
            }
            Ok(out)
        });
        (self.ahead, self.ahead_filled) = outer;
        r
    }

    fn parse_module_items(&mut self, forms: &[Syntax]) -> R<Vec<ModItem>> {
        let outer_runs = std::mem::replace(&mut self.run_items, 0);
        let r = self.parse_module_items_counted(forms);
        self.run_items = outer_runs;
        r
    }

    fn parse_module_items_counted(&mut self, forms: &[Syntax]) -> R<Vec<ModItem>> {
        let mut out = Vec::new();
        // Each `(include m)`, and where each item's values are written (a
        // `define-rec`'s, each binding's), for `with_includes`.
        let (mut includes, mut spans): (Vec<(fixpt_read::Span, ExpId, bool)>, Vec<Vec<fixpt_read::Span>>) = (Vec::new(), Vec::new());
        // The forms to read, the first last, each hidden or not (`(hide
        // item …)`, `TODO.md` §69): the module's own borrowed, not copied
        // (`TODO.md` §126), and what a `hide` expands to owned.
        let work: Vec<(std::borrow::Cow<'_, Syntax>, bool)> = forms.iter().rev().map(|f| (std::borrow::Cow::Borrowed(f), false)).collect();
        // A module with `include`s, in a `hide` or not: their types are in
        // scope in its items (`include_scope`).
        let includes_here = forms.iter().any(|f| self.includes_in(f));
        self.include_scope += usize::from(includes_here);
        let r = self.module_items_from(work, &mut out, &mut includes, &mut spans);
        self.include_scope -= usize::from(includes_here);
        r?;
        if !includes.is_empty() {
            self.with_includes(&mut out, &spans, includes);
        }
        Ok(out)
    }

    /// Whether form `f` is an `(include m)`, or a `hide` holding one.
    fn includes_in(&self, f: &Syntax) -> bool {
        let items = f.as_proper_list().unwrap_or(&[]);
        match self.head(items) {
            Some("include") => true,
            Some("hide") => items[1..].iter().any(|g| self.includes_in(g)),
            _ => false,
        }
    }

    /// `parse_module_items`' work: the forms of `work`, the first last, read
    /// into `out`, `includes` and `spans`.
    #[allow(clippy::type_complexity)]
    fn module_items_from(
        &mut self,
        mut work: Vec<(std::borrow::Cow<'_, Syntax>, bool)>,
        out: &mut Vec<ModItem>,
        includes: &mut Vec<(fixpt_read::Span, ExpId, bool)>,
        spans: &mut Vec<Vec<fixpt_read::Span>>,
    ) -> R<()> {
        while let Some((f, hidden)) = work.pop() {
            let f: &Syntax = &f;
            // A string: a comment, read past (in a `hide` too, and among a
            // module file's forms).
            if f.as_str().is_some() {
                continue;
            }
            // An expression: run for what it does as the module is made, in
            // order, as a hidden definition of its value (Heist's,
            // 2026-10-28; `parser.fx`'s `run-item`).
            if !is_item_form(f, &self.interner) {
                let n = self.run_items;
                self.run_items += 1;
                let sym = |c: &mut Self, s: &str| Syntax::symbol(f.span, c.interner.intern(s));
                let define = Syntax::list(f.span, vec![sym(self, "define"), sym(self, &format!("%run-{n}")), f.clone()]);
                work.push((std::borrow::Cow::Owned(Syntax::list(f.span, vec![sym(self, "hide"), define])), hidden));
                continue;
            }
            let parts = self.items(f, "a module's definition")?;
            // `(hide item …)`: its items, their `define-datatype`s expanded,
            // each hidden.
            if self.head(&parts) == Some("hide") {
                let mut inner = Vec::new();
                for item in &parts[1..] {
                    self.expand_datatype(item.clone(), &mut inner)?;
                }
                work.extend(inner.into_iter().rev().map(|item| (std::borrow::Cow::Owned(item), true)));
                continue;
            }
            // Its files named in types, loaded first (`type_loads`).
            self.type_loads(f)?;
            let before = out.len();
            let name_of = |p: &Self, s: &Syntax| s.as_symbol().ok_or_else(|| FxError::at(s.span, "a name")).map(|n| (n, p.name(n).to_string()));
            match (self.head(&parts), &parts[..]) {
                (Some("define-generative"), [_, n, rep]) => {
                    // `(define-generative (t (p k) …) rep)`: a type
                    // constructor, its representation a function of the
                    // parameters (`crate::kinds`).
                    let (n, params) = match n.as_proper_list() {
                        Some([n, ps @ ..]) if !ps.is_empty() => (n, Some(Syntax::list(f.span, ps.to_vec()))),
                        _ => (n, None),
                    };
                    let (name, text) = name_of(self, n)?;
                    let depth = self.dscope.len();
                    let binders = match &params {
                        Some(ps) => self.parse_binders(ps)?,
                        None => Vec::new(),
                    };
                    self.dscope.truncate(depth);
                    let kind = if binders.is_empty() { Kind::Type } else { self.arena.arrow(binders.iter().map(|(_, k)| *k).collect(), Kind::Type) };
                    let var = self.arena.dvar_of(name, kind);
                    if kind != Kind::Type {
                        self.abstract_funs.insert(var);
                    }
                    self.dscope.push((name, DScope::Var(var, kind)));
                    let inner = self.dscope.len();
                    for (v, k) in &binders {
                        self.dscope.push((self.arena.dvar_name(*v), DScope::Var(*v, *k)));
                    }
                    let rep = self.parse_type(rep);
                    self.dscope.truncate(inner);
                    let rep = rep?;
                    let rep = if binders.is_empty() { rep } else { self.arena.ty(Ty::Lam { params: binders, body: D::Type(rep) }) };
                    let (up, down) = (self.interner.intern(&format!("up-{text}")), self.interner.intern(&format!("down-{text}")));
                    // Each conversion the identity, made as a closure is.
                    let x = self.interner.intern("x");
                    let identity = |p: &mut Self| {
                        let body = p.arena.exp(f.span, Exp::Var(x));
                        p.arena.exp(f.span, Exp::Lambda { params: vec![(x, None)], body })
                    };
                    let (up_fn, down_fn) = (identity(self), identity(self));
                    out.push(ModItem::Abs { name, var, rep, up, down, up_fn, down_fn });
                }
                // `(define-type (d (p k) …) T)`, a parameterised
                // description, is `(define-type d (dlambda ((p k) …) T))`:
                // what a `define-datatype` with parameters expands to, in a
                // `load-module`'s file too (PLAN.md Q13, O15). As the FX-26
                // parser's `parse-module-item`.
                (Some("define-type"), [_, head, t]) if head.as_proper_list().is_some_and(|h| h.len() > 1) => {
                    let h = head.as_proper_list().unwrap_or(&[]);
                    let (name, _) = name_of(self, &h[0])?;
                    let dlambda = Syntax::symbol(head.span, self.interner.intern("dlambda"));
                    let fun = Syntax::list(f.span, vec![dlambda, Syntax::list(head.span, h[1..].to_vec()), t.clone()]);
                    let ty = self.parse_fun(&fun, None)?;
                    self.dscope.push((name, DScope::Fun(ty)));
                    out.push(ModItem::Desc { name, ty });
                }
                (Some("define-type"), [_, n, t]) if self.head(t.as_proper_list().unwrap_or(&[])) == Some("dlambda") => {
                    let (name, _) = name_of(self, n)?;
                    let ty = self.parse_fun(t, None)?;
                    self.dscope.push((name, DScope::Fun(ty)));
                    out.push(ModItem::Desc { name, ty });
                }
                // As a program's: declared ahead, or a knot of its own.
                (Some("define-type"), [_, n, t]) => {
                    let (name, _) = name_of(self, n)?;
                    let ty = self.define_type(name, t, t.span)?;
                    out.push(ModItem::Desc { name, ty });
                }
                // `(define-effect e E)`: a transparent description of an
                // effect, as `define-type`'s of a type: `(desc e E)` in the
                // module's type, `(select m e)` outside.
                (Some("define-effect"), [_, n, e]) => {
                    let (name, _) = name_of(self, n)?;
                    let e = self.parse_effect(e)?;
                    self.dscope.push((name, DScope::Eff(e.clone())));
                    let ty = self.effect_desc(e);
                    out.push(ModItem::Desc { name, ty });
                }
                (Some("define"), [_, n, init]) => {
                    let (name, _) = name_of(self, n)?;
                    out.push(ModItem::Val { name, ty: None, init: self.parse_exp(init)?, infer: false });
                }
                (Some(d @ ("define" | "define*")), [_, n, t, init]) => {
                    let infer = d == "define*";
                    let (name, _) = name_of(self, n)?;
                    self.arrow_star = self.written_arrow_star(t);
                    if infer && self.arrow_star {
                        self.arrow_star = false;
                        return Err(FxError::at(t.span, "`define*` and `->*` each find what a procedure does: write one"));
                    }
                    let ty = self.parse_type(t)?;
                    out.push(ModItem::Val { name, ty: Some(ty), init: self.parse_exp(init)?, infer });
                }
                // `(include m)` (`TODO.md` §69): `m`'s values the module's own.
                (Some("include"), [_, m]) => {
                    includes.push((f.span, self.parse_exp(m)?, hidden));
                    continue;
                }
                (Some("define-rec"), [_, bs @ ..]) => {
                    let mut group = Vec::new();
                    spans.push(bs.iter().map(|b| b.span).collect());
                    for b in bs {
                        let triple = self.items(b, "`(name type expression)`")?.to_vec();
                        let [n, t, init] = &triple[..] else {
                            return Err(FxError::at(b.span, "`(define-rec (name type expression) …)`"));
                        };
                        let (name, _) = name_of(self, n)?;
                        self.arrow_star = self.written_arrow_star(t);
                        let ty = self.parse_type(t)?;
                        group.push((name, ty, self.parse_exp(init)?));
                    }
                    out.push(ModItem::Rec(group));
                }
                _ => {
                    return Err(FxError::at(
                        f.span,
                        "a module holds `(define-generative t T)`, `(define-type d T)`, `(define-effect e E)`, `(define x [T] e)`, `(define* f T e)`, `(define-rec (f T e) …)`, `(include m)` and `(hide item …)`",
                    ));
                }
            }
            spans.resize(out.len(), vec![f.span]);
            // Each name a hidden item defines, marked by a type of its own:
            // a type's `%hidden:name`, a value's `%hiddenv:name`, as a type
            // and a value may share a name; types, so that no compiler makes
            // a value of them. The checkers leave them out of the module's
            // type.
            if hidden {
                let mut names = Vec::new();
                for item in &out[before..] {
                    match item {
                        ModItem::Abs { name, up, down, .. } => names.extend([(*name, false), (*up, true), (*down, true)]),
                        ModItem::Desc { name, .. } => names.push((*name, false)),
                        ModItem::Val { name, .. } => names.push((*name, true)),
                        ModItem::Rec(bs) => names.extend(bs.iter().map(|(n, _, _)| (*n, true))),
                    }
                }
                for (n, value) in names {
                    let name = self.interner.intern(&format!("{}{}", if value { "%hiddenv:" } else { "%hidden:" }, self.name(n)));
                    out.push(ModItem::Desc { name, ty: self.unit });
                }
                spans.resize(out.len(), vec![f.span]);
            }
        }
        Ok(())
    }

    /// A module's `(include m)`s (`TODO.md` §69): one hidden item first,
    /// `%include`, a module of hidden items `%include-0`, … that are the
    /// modules included, made before the module's own items and seeing
    /// none of them; each own item's value in a `(with %include …)` (a
    /// lambda's body, so that it stays a lambda), its place the item's, as
    /// the compilers find facts by place. The checkers make the module's
    /// type of its own values and those (`Checker::included`).
    fn with_includes(&mut self, out: &mut Vec<ModItem>, spans: &[Vec<fixpt_read::Span>], includes: Vec<(fixpt_read::Span, ExpId, bool)>) {
        let inc = self.interner.intern("%include");
        let first = includes[0].0;
        // A hidden one's, `%hinclude-k`: its values in scope, not in the
        // module's type.
        let bucket = includes
            .into_iter()
            .enumerate()
            .map(|(k, (_, m, hidden))| {
                let name = self.interner.intern(&format!("%{}include-{k}", if hidden { "h" } else { "" }));
                ModItem::Val { name, ty: None, init: m, infer: false }
            })
            .collect();
        let bucket = self.arena.exp(first, Exp::Module(bucket));
        for (item, at) in out.iter_mut().zip(spans) {
            match item {
                ModItem::Val { init, .. } => *init = self.in_includes(*init, at[0], inc),
                ModItem::Rec(bs) => {
                    for (b, span) in bs.iter_mut().zip(at) {
                        b.2 = self.in_includes(b.2, *span, inc);
                    }
                }
                ModItem::Abs { .. } | ModItem::Desc { .. } => {}
            }
        }
        out.insert(0, ModItem::Val { name: inc, ty: None, init: bucket, infer: false });
    }

    /// `x` in `(with inc …)` at `span`: a lambda's body, under any
    /// `plambda`, `the` or region lambda, so that it stays a lambda.
    fn in_includes(&mut self, x: ExpId, span: fixpt_read::Span, inc: Sym) -> ExpId {
        match self.arena.exp_at(x).clone() {
            Exp::Lambda { params, body } => {
                let body = self.arena.exp(span, Exp::With { module: inc, body });
                self.arena.replace_exp(x, Exp::Lambda { params, body });
                x
            }
            Exp::PLambda { binders, body } => {
                let body = self.in_includes(body, span, inc);
                self.arena.replace_exp(x, Exp::PLambda { binders, body });
                x
            }
            Exp::The { ty, exp } => {
                let exp = self.in_includes(exp, span, inc);
                self.arena.replace_exp(x, Exp::The { ty, exp });
                x
            }
            Exp::RLambda { region, lambda } => {
                let lambda = self.in_includes(lambda, span, inc);
                self.arena.replace_exp(x, Exp::RLambda { region, lambda });
                x
            }
            _ => self.arena.exp(span, Exp::With { module: inc, body: x }),
        }
    }

    pub(crate) fn label(&mut self, s: &Syntax) -> R<Sym> {
        if let Some(x) = s.as_symbol() {
            return Ok(x);
        }
        match self.literal_int(s) {
            Some(n) if n >= 0 => Ok(self.interner.intern(&n.to_string())),
            _ => Err(FxError::at(s.span, "a label is a name or a natural number")),
        }
    }

    /// `(tagcase e (tag x body…) … [(else y body…)])`.
    fn parse_tagcase(&mut self, span: fixpt_read::Span, items: &[Syntax]) -> R<ExpId> {
        let Some((scrutinee, clauses)) = items.split_first() else {
            return Err(FxError::at(span, "`(tagcase expression (tag name body …) …)`"));
        };
        let scrutinee = self.parse_exp(scrutinee)?;
        let mut arms: Vec<Arm> = Vec::new();
        let mut els = None;
        for (i, c) in clauses.iter().enumerate() {
            // An arm still to be written: an `else` whose body is the hole,
            // so that what it binds says which tags are left.
            if let Some(h) = self.holes
                && c.as_symbol() == Some(h.exp)
            {
                let body = self.arena.exp(c.span, Exp::Var(h.arm));
                els = Some((h.arm_var, body));
                break;
            }
            let parts = self.items(c, "a tagcase arm")?.to_vec();
            let [tag, bind, body @ ..] = &parts[..] else {
                return Err(FxError::at(c.span, "a tagcase arm is `(tag name body …)`"));
            };
            if body.is_empty() {
                return Err(FxError::at(c.span, "a tagcase arm needs a body"));
            }
            if tag.as_symbol().map(|t| self.name(t)) == Some("else") {
                if i + 1 != clauses.len() {
                    return Err(FxError::at(c.span, "`else` must be the last arm"));
                }
                let Some(y) = bind.as_symbol() else {
                    return Err(FxError::at(bind.span, "`else` binds one name"));
                };
                els = Some((y, self.parse_body(c.span, body)?));
                continue;
            }
            let tag = self.label(tag)?;
            if arms.iter().any(|a| a.tag == tag) {
                return Err(FxError::at(c.span, format!("`{}` has two arms", self.name(tag))));
            }
            let bind = match (bind.as_symbol(), &bind.datum) {
                (Some(x), _) => ArmBind::Value(x),
                (None, Datum::Nil) => ArmBind::Fields(Vec::new()),
                _ => {
                    let names = self.items(bind, "the names an arm binds")?;
                    let names = names
                        .iter()
                        .map(|n| n.as_symbol().ok_or_else(|| FxError::at(n.span, "a name")))
                        .collect::<R<Vec<_>>>()?;
                    ArmBind::Fields(names)
                }
            };
            let body = self.parse_body(c.span, body)?;
            arms.push(Arm { tag, bind, body });
        }
        Ok(self.arena.exp(span, Exp::TagCase { scrutinee, arms, els }))
    }

    /// A bloblet form; see [`BlobletOp`].
    /// A `lambda`'s parameters and body, parsed.
    fn parse_lambda(&mut self, span: fixpt_read::Span, params: &Syntax, body: &[Syntax]) -> R<ExpId> {
        let params = match &params.datum {
            Datum::Nil => Vec::new(),
            _ => self
                .items(params, "parameters")?
                .to_vec()
                .iter()
                .map(|p| {
                    if self.holes.is_some_and(|h| p.as_symbol() == Some(h.exp)) {
                        return Err(FxError::at(p.span, "a parameter is `name` or `(name type)`"));
                    }
                    if let Some(name) = p.as_symbol() {
                        return Ok((name, None));
                    }
                    let pair = self.items(p, "a parameter")?.to_vec();
                    let [name, ty] = &pair[..] else {
                        return Err(FxError::at(p.span, "a parameter is `name` or `(name type)`"));
                    };
                    let name = name.as_symbol().ok_or_else(|| FxError::at(name.span, "a name"))?;
                    Ok((name, Some(self.parse_type(ty)?)))
                })
                .collect::<R<Vec<_>>>()?,
        };
        let body = self.parse_body(span, body)?;
        Ok(self.arena.exp(span, Exp::Lambda { params, body }))
    }

    fn parse_bloblet(&mut self, span: fixpt_read::Span, name: &str, args: &[Syntax]) -> R<ExpId> {
        let index = |p: &Self, s: &Syntax| -> R<usize> {
            match p.literal_int(s) {
                Some(i) if i >= 0 => Ok(i as usize),
                _ => Err(FxError::at(s.span, "a field index is a literal, non-negative integer")),
            }
        };
        let (op, rest): (BlobletOp, &[Syntax]) = match (name, args) {
            ("make-bloblet", [_, ..]) => (BlobletOp::Make, args),
            ("rmake-bloblet", [_, _, ..]) => (BlobletOp::RMake, args),
            ("bloblet-ref", [b, i]) => (BlobletOp::Ref(index(self, i)?), std::slice::from_ref(b)),
            ("bloblet-set!", [b, i, v]) => {
                let i = index(self, i)?;
                let args = vec![self.parse_exp(b)?, self.parse_exp(v)?];
                return Ok(self.arena.exp(span, Exp::Bloblet { op: BlobletOp::Set(i), args }));
            }
            ("bloblet-freeze", [_]) => (BlobletOp::Freeze, args),
            ("bloblet-byte", [_, _]) => (BlobletOp::Byte, args),
            ("bloblet-set-byte!", [_, _, _]) => (BlobletOp::SetByte, args),
            ("bloblet-bytes", [_]) => (BlobletOp::Bytes, args),
            ("blobref-at", [_, _]) => (BlobletOp::RefAt, args),
            ("blobref+", [_, _]) => (BlobletOp::RefAdd, args),
            ("blobref-owner", [_]) => (BlobletOp::RefOwner, args),
            ("blobref-offset", [_]) => (BlobletOp::RefOffset, args),
            ("blobref-get", [_]) => (BlobletOp::RefGet, args),
            ("blobref-set!", [_, _]) => (BlobletOp::RefSet, args),
            ("blobref-index", [_, _]) => (BlobletOp::RefIndex, args),
            ("blobref-length", [_]) => (BlobletOp::RefLength, args),
            ("blobref-variant!", [_, _]) => (BlobletOp::RefVariant, args),
            _ => {
                let shape = match name {
                    "make-bloblet" => "(make-bloblet bytes field …)",
                    "rmake-bloblet" => "(rmake-bloblet region bytes field …)",
                    "bloblet-ref" => "(bloblet-ref bloblet index)",
                    "bloblet-set!" => "(bloblet-set! bloblet index value)",
                    "bloblet-freeze" => "(bloblet-freeze bloblet)",
                    "bloblet-byte" => "(bloblet-byte bloblet i)",
                    "bloblet-set-byte!" => "(bloblet-set-byte! bloblet i byte)",
                    "blobref-at" => "(blobref-at bloblet offset)",
                    "blobref+" => "(blobref+ blobref bytes)",
                    "blobref-owner" => "(blobref-owner blobref)",
                    "blobref-offset" => "(blobref-offset blobref)",
                    "blobref-get" => "(blobref-get blobref)",
                    "blobref-set!" => "(blobref-set! blobref value)",
                    "blobref-index" => "(blobref-index blobref i)",
                    "blobref-length" => "(blobref-length blobref)",
                    "blobref-variant!" => "(blobref-variant! blobref 'label)",
                    _ => "(bloblet-bytes bloblet)",
                };
                return Err(FxError::at(span, format!("`{shape}`")));
            }
        };
        let args = rest.iter().map(|a| self.parse_exp(a)).collect::<R<Vec<_>>>()?;
        Ok(self.arena.exp(span, Exp::Bloblet { op, args }))
    }

    /// One or more expressions: an implicit `begin`.
    fn parse_body(&mut self, span: fixpt_read::Span, forms: &[Syntax]) -> R<ExpId> {
        match forms {
            [] => Err(FxError::at(span, "an empty body")),
            [one] => self.parse_exp(one),
            many => {
                let es = many.iter().map(|f| self.parse_exp(f)).collect::<R<Vec<_>>>()?;
                Ok(self.arena.exp(span, Exp::Begin(es)))
            }
        }
    }
}

/// What a `case` tree's leaves give: the clause's index, for a second
/// search to choose its body by; or, a datum to a clause and an `else` of
/// one atom, the body itself, the `else` (its syntax) made at each leaf.
enum CaseLeaves<'a> {
    Index,
    Bodies(&'a [ExpId], &'a (fixpt_read::Span, Syntax)),
}

/// The shapes `typecase` tests (`check::SHAPES`), each with its standard
/// predicate: those that have one.
impl Checker {
    /// What builds datum `x`, quoted (`depth` none) or quasiquoted at
    /// `depth` (TODO §51): atoms as themselves, symbols quoted, `()` as
    /// `nil`, lists as `cons`es, vectors and bytevectors from lists; a
    /// list or vector in `(the datum …)`. Under `quasiquote`, `(unquote e)`
    /// at depth 1 is `e`, and `(unquote-splicing e)` is `e` appended to
    /// what follows; nested `quasiquote`s count depth as R7RS does. The
    /// standard operations, through `#%fx`, so a program's own `cons` changes
    /// nothing; a bare `'()` is the plain `nil`, an empty list of any type. A
    /// datum is immutable and acyclic, so building it anew each time differs
    /// from Scheme's constant only in identity.
    pub(crate) fn quoted(&mut self, x: &Syntax, depth: Option<u32>) -> Syntax {
        let built = self.quoted_in(x, depth);
        match &x.datum {
            Datum::List { .. } | Datum::Vector(_) | Datum::Bytevector(_) if !matches!(self.unquoted(x, depth), Some(_)) => {
                let the = self.named(x.span, "the");
                let datum = self.named(x.span, "datum");
                // A quote's, not a quasiquote's, marked (`%quote`):
                // everything in it the rewrite's, made once where it is all
                // literals.
                let built = if depth.is_none() {
                    self.call(x.span, "%quote", vec![built])
                } else {
                    built
                };
                Syntax::list(x.span, vec![the, datum, built])
            }
            _ => built,
        }
    }

    /// FX-26 has no way to read a bytevector's bytes, so the parser written
    /// in it could not build a quoted one: refused in both, for now.
    fn no_bytevector(x: &Syntax) -> R<()> {
        match &x.datum {
            Datum::Bytevector(_) => Err(FxError::at(x.span, "a bytevector cannot be quoted yet")),
            Datum::List { items, tail } => {
                items.iter().try_for_each(Self::no_bytevector)?;
                tail.as_deref().map_or(Ok(()), Self::no_bytevector)
            }
            Datum::Vector(items) => items.iter().try_for_each(Self::no_bytevector),
            _ => Ok(()),
        }
    }

    fn named(&mut self, span: fixpt_read::Span, name: &str) -> Syntax {
        let s = self.interner.intern(name);
        Syntax::symbol(span, s)
    }

    /// `(with #%fx name)`: the standard `name`, whatever a program binds it
    /// to.
    fn standard_named(&mut self, span: fixpt_read::Span, name: &str) -> Syntax {
        let (with, fx, n) = (self.named(span, "with"), self.named(span, "#%fx"), self.named(span, name));
        Syntax::list(span, vec![with, fx, n])
    }

    fn call(&mut self, span: fixpt_read::Span, op: &str, mut args: Vec<Syntax>) -> Syntax {
        let mut items = vec![self.standard_named(span, op)];
        items.append(&mut args);
        Syntax::list(span, items)
    }

    /// `(form e)`, where `form` is `unquote` or `unquote-splicing`: `e`.
    fn unquote_of<'a>(&self, x: &'a Syntax, form: &str) -> Option<&'a Syntax> {
        match &x.datum {
            Datum::List { items, tail: None } => match &items[..] {
                [h, e] if h.as_symbol().is_some_and(|h| self.name(h) == form) => Some(e),
                _ => None,
            },
            _ => None,
        }
    }

    /// `x`'s expression, if `x` is `(unquote e)` at depth 1.
    fn unquoted<'a>(&self, x: &'a Syntax, depth: Option<u32>) -> Option<&'a Syntax> {
        if depth == Some(1) { self.unquote_of(x, "unquote") } else { None }
    }

    /// Whether no `unquote` or `unquote-splicing` at depth 1 is in `x`,
    /// quasiquoted at `depth`: then it is a constant.
    fn unquote_free(&self, x: &Syntax, depth: Option<u32>) -> bool {
        if self.unquoted(x, depth).is_some() {
            return false;
        }
        match &x.datum {
            Datum::List { items, tail } => {
                let inner = self.quasi_inner(items, depth);
                items.iter().enumerate().all(|(i, item)| self.item_free(item, if i == 0 { depth } else { inner }))
                    && tail.as_deref().is_none_or(|t| self.unquote_free(t, depth))
            }
            Datum::Vector(items) => items.iter().all(|item| self.item_free(item, depth)),
            _ => true,
        }
    }

    /// Whether list item `x`, at `depth`, is neither spliced nor reached by
    /// an `unquote`.
    fn item_free(&self, x: &Syntax, depth: Option<u32>) -> bool {
        !(depth == Some(1) && self.unquote_of(x, "unquote-splicing").is_some()) && self.unquote_free(x, depth)
    }

    /// The depth a list's items after its head are at: a nested
    /// `quasiquote` deepens; an `unquote` (or `unquote-splicing`) not at
    /// depth 1 shallows.
    fn quasi_inner(&self, items: &[Syntax], depth: Option<u32>) -> Option<u32> {
        let head = items.first().and_then(|h| h.as_symbol()).map(|h| self.name(h));
        match (depth, head) {
            (Some(d), Some("quasiquote")) if items.len() == 2 => Some(d + 1),
            (Some(d), Some("unquote" | "unquote-splicing")) if items.len() == 2 && d > 1 => Some(d - 1),
            _ => depth,
        }
    }

    fn quoted_in(&mut self, x: &Syntax, depth: Option<u32>) -> Syntax {
        let span = x.span;
        if let Some(e) = self.unquoted(x, depth) {
            return e.clone();
        }
        // Under a quasiquote, a list or vector no unquote reaches is a
        // constant: a quote, made once (`%quote`).
        if depth.is_some() && matches!(x.datum, Datum::List { .. } | Datum::Vector(_)) && self.unquote_free(x, depth) {
            let built = self.quoted_in(x, None);
            return self.call(span, "%quote", vec![built]);
        }
        match &x.datum {
            Datum::Symbol(s) => match self.name(*s) {
                // `#t` and `#f` are literals, as the FX-26 reader gives them.
                "#t" | "#f" => x.clone(),
                _ => {
                    let q = self.named(span, "quote");
                    Syntax::list(span, vec![q, x.clone()])
                }
            },
            Datum::Nil => self.named(span, "nil"),
            Datum::Bool(_) | Datum::Number(_) | Datum::Char(_) | Datum::Str(_) => x.clone(),
            Datum::List { items, tail } => {
                let inner = self.quasi_inner(items, depth);
                // Under a quasiquote, the items after the last that an
                // unquote reaches, with the tail, are a constant: one quote
                // (`k` the first of them), made once.
                let mut k = items.len();
                if depth.is_some() && tail.as_deref().is_none_or(|t| self.unquote_free(t, depth)) {
                    while k > 1 && self.item_free(&items[k - 1], inner) {
                        k -= 1;
                    }
                }
                // `nil` at the list, each `cons` from its item, a constant
                // suffix's `%quote` from its first item to the end.
                let mut acc = if k < items.len() {
                    let rest = Syntax::new(span, Datum::List { items: items[k..].to_vec(), tail: tail.clone() });
                    let built = self.quoted_in(&rest, None);
                    self.call(fixpt_read::Span { start: items[k].span.start, ..span }, "%quote", vec![built])
                } else {
                    match tail {
                        Some(t) => self.quoted_in(t, depth),
                        None => self.standard_named(span, "nil"),
                    }
                };
                for (i, item) in items[..k].iter().enumerate().rev() {
                    let d = if i == 0 { depth } else { inner };
                    if d == Some(1)
                        && let Some(e) = self.unquote_of(item, "unquote-splicing")
                    {
                        let the = self.named(span, "the");
                        let ty = {
                            let (l, d, a) = (self.named(span, "listof"), self.named(span, "datum"), self.named(span, "acyclic"));
                            Syntax::list(span, vec![l, d, a])
                        };
                        let rest = Syntax::list(span, vec![the, ty, acc]);
                        acc = self.call(item.span, "append", vec![e.clone(), rest]);
                        continue;
                    }
                    let q = self.quoted_in(item, d);
                    acc = self.call(item.span, "cons", vec![q, acc]);
                }
                acc
            }
            Datum::Vector(items) => {
                let list = Syntax::new(span, Datum::List { items: items.clone(), tail: None });
                let l = self.quoted_in(&list, depth);
                self.call(span, "datum-list->vector", vec![l])
            }
            // Refused before (`no_bytevector`).
            Datum::Bytevector(_) => x.clone(),
        }
    }
}

const TYPECASE_SHAPES: &[(&str, &str)] = &[
    ("int", "int?"),
    ("char", "char?"),
    ("bool", "bool?"),
    ("nil", "null?"),
    ("pair", "pair?"),
    ("string", "string?"),
    ("symbol", "symbol?"),
    ("procedure", "procedure?"),
    ("bloblet", "array?"),
    ("f64", "f64?"),
    ("f32", "f32?"),
    ("box", "ref?"),
    ("sum", "sum?"),
    ("product", "product?"),
    ("vector", "vector?"),
    ("bytevector", "bytevector?"),
];

fn typecase_predicate(shape: &str) -> Option<&'static str> {
    TYPECASE_SHAPES.iter().find(|(s, _)| *s == shape).map(|(_, p)| *p)
}

/// The binders of `(module-parameters (binder …))`, if `f` is one.
pub(crate) fn module_parameters_of(f: &Syntax, interner: &fixpt_read::Interner) -> Option<Vec<Syntax>> {
    match f.as_proper_list()? {
        [h, bs] if h.as_symbol().is_some_and(|h| interner.name(h) == "module-parameters") => Some(bs.as_proper_list()?.to_vec()),
        _ => None,
    }
}

/// Whether binder `b` of a `module-parameters` binds a description, `(name
/// kind)` or `(r region p)`; else it is `(m T)` or `(m T qualified)`, a
/// module parameter.
pub(crate) fn binder_is_kind(b: &Syntax, interner: &fixpt_read::Interner) -> bool {
    match b.as_proper_list() {
        Some([_, k]) => is_kind_form(k, interner),
        Some([_, k, q]) => is_kind_form(k, interner) || !is_qualified(q, interner),
        _ => true,
    }
}

/// `qualified`, a module parameter's mark that it is not included: its
/// names are reached by `with` or `import` (Heist's, 2026-10-28).
fn is_qualified(q: &Syntax, interner: &fixpt_read::Interner) -> bool {
    q.as_symbol().is_some_and(|q| interner.name(q) == "qualified")
}

fn is_kind_form(k: &Syntax, interner: &fixpt_read::Interner) -> bool {
    match k.as_proper_list() {
        Some([h, ..]) => h.as_symbol().is_some_and(|h| interner.name(h) == "=>"),
        _ => k.as_symbol().is_some_and(|k| {
            matches!(interner.name(k), "region" | "place" | "effect" | "type" | "data" | "sendable" | "flat" | "size" | "conv")
        }),
    }
}

/// Whether forms `forms` are a file of module parameters: its first form a
/// `module-parameters` with a module among its binders.
pub(crate) fn takes_modules(forms: &[Syntax], interner: &fixpt_read::Interner) -> bool {
    forms
        .first()
        .and_then(|f| module_parameters_of(f, interner))
        .is_some_and(|bs| bs.iter().any(|b| !binder_is_kind(b, interner)))
}

/// Whether the file at `at`, `path` as written, is a file of module
/// parameters, read apart (as the driver reads it, `syn::supply_loaded_in`).
pub(crate) fn takes_modules_at(at: &std::path::Path, path: &str) -> bool {
    let text = match crate::built_in_module(path) {
        Some(t) => t.to_string(),
        None => match std::fs::read_to_string(at) {
            Ok(t) => t,
            Err(_) => return false,
        },
    };
    // Only a file that begins so: the rest is not read.
    if !text.contains("module-parameters") {
        return false;
    }
    let mut interner = fixpt_read::Interner::new();
    match fixpt_read::Reader::new(&text, fixpt_read::FileId(0), fixpt_read::SyntaxProfile::FX26, &mut interner).read_all() {
        Ok(forms) => takes_modules(&forms, &interner),
        Err(_) => false,
    }
}

/// Whether module item `f` is a form a module item may be, by its head
/// (the parsers refuse it if it is not well made); else a list is an
/// expression, run for what it does as the module is made. An atom is
/// refused as it was.
pub(crate) fn is_item_form(f: &Syntax, interner: &fixpt_read::Interner) -> bool {
    match f.as_proper_list() {
        Some([]) | None => true,
        Some([h, ..]) => h.as_symbol().is_some_and(|h| {
            matches!(
                interner.name(h),
                "define-generative" | "define-type" | "define-effect" | "define" | "define*" | "include" | "define-rec" | "hide" | "define-datatype" | "import"
            )
        }),
    }
}
