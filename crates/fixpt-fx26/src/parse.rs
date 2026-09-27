//! Syntax to the kernel.
//!
//! The forms are FX-87's (`docs/fx26.md`, "The kernel"): n-ary forms, binder
//! lists in parentheses — `(plambda ((t type)) …)` — and `@name` for a region
//! constant. The lexical syntax is FX-26's own, `SyntaxProfile::FX26`. `let` and `begin` are derived forms, and `lambda` and `letrec`
//! bodies are implicit `begin`s. A `lambda` parameter may be a bare name, when
//! the `lambda` is checked against a type that says what it is.

use crate::ast::{Arm, ArmBind, Atom, BlobletOp, D, DVar, Effect, Exp, ExpId, Kind, Region, RegionForm, Ty, TyId};
use crate::check::Checker;
use crate::error::{FxError, R};
use fixpt_read::{Datum, Sym, Syntax};

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
    /// A name bound by `define-effect`: an effect.
    Eff(crate::ast::Effect),
    /// A region constant `private-regions` made the program's own: `@s` in
    /// the program is this fresh region, which nothing else can name.
    Private(Region),
}

impl Checker {
    fn name(&self, s: Sym) -> &str {
        self.interner.name(s)
    }

    /// The region `@name` stands for: the program's own, if `private-regions`
    /// declared it, and otherwise the constant of that name.
    fn region_constant(&self, sym: Sym) -> Region {
        match self.lookup_desc(sym) {
            Some(DScope::Private(r)) => r,
            _ => Region::Const(sym),
        }
    }

    fn lookup_desc(&self, s: Sym) -> Option<DScope> {
        self.dscope.iter().rev().find(|(n, _)| *n == s).map(|(_, d)| d.clone())
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

    fn head(&self, items: &[Syntax]) -> Option<&str> {
        items.first().and_then(|h| h.as_symbol()).map(|h| self.name(h))
    }

    // --------------------------------------------------------------- kinds
    fn parse_kind(&self, s: &Syntax) -> R<Kind> {
        match s.as_symbol().map(|k| self.name(k)) {
            Some("region") => Ok(Kind::Region),
            Some("place") => Ok(Kind::Place),
            Some("effect") => Ok(Kind::Effect),
            Some("type") => Ok(Kind::Type),
            _ => Err(FxError::at(s.span, "a kind is `region`, `place`, `effect` or `type`")),
        }
    }

    /// `((I K) …)`, binding each name for the rest of the parse.
    fn parse_binders(&mut self, s: &Syntax) -> R<Vec<(DVar, Kind)>> {
        let mut out = Vec::new();
        for b in self.items(s, "binders")? {
            let pair = self.items(b, "a binder")?;
            let [name, kind] = pair else {
                return Err(FxError::at(b.span, "a binder is `(name kind)`"));
            };
            let name = name.as_symbol().ok_or_else(|| FxError::at(name.span, "a binder's name"))?;
            let kind = self.parse_kind(kind)?;
            let v = self.arena.dvar_of(name, kind);
            self.dscope.push((name, DScope::Var(v, kind)));
            out.push((v, kind));
        }
        Ok(out)
    }

    // ------------------------------------------------------------- regions
    pub(crate) fn parse_region(&self, s: &Syntax) -> R<Region> {
        let Some(sym) = s.as_symbol() else {
            return Err(FxError::at(s.span, "expected a region"));
        };
        if self.name(sym).starts_with('@') {
            return Ok(self.region_constant(sym));
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

    // ------------------------------------------------------------- effects
    pub(crate) fn parse_effect(&self, s: &Syntax) -> R<Effect> {
        if let Some(sym) = s.as_symbol() {
            if self.name(sym) == "pure" {
                return Ok(Effect::pure());
            }
            return match self.lookup_desc(sym) {
                Some(DScope::Var(v, Kind::Effect)) => Ok(Effect::atom(Atom::Var(v))),
                Some(DScope::Eff(e)) => Ok(e),
                _ => Err(FxError::at(s.span, format!("`{}` is not an effect", self.name(sym)))),
            };
        }
        let items = self.items(s, "an effect")?;
        let head = self.head(items).unwrap_or("");
        let atom = |c: fn(Region) -> Atom| -> R<Effect> {
            let [_, r] = items else {
                return Err(FxError::at(s.span, format!("`({head} region)`")));
            };
            Ok(Effect::atom(c(self.parse_region(r)?)))
        };
        match head {
            "read" => atom(Atom::Read),
            "write" => atom(Atom::Write),
            "alloc" => atom(Atom::Alloc),
            "goto" => atom(Atom::Goto),
            "comefrom" => atom(Atom::Comefrom),
            "await" => atom(Atom::Await),
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
        if let Some(sym) = s.as_symbol() {
            let name = self.name(sym);
            if name == "void" {
                return Ok(self.void);
            }
            if let Some(&t) = self.base.get(&sym) {
                return Ok(t);
            }
            return match self.lookup_desc(sym) {
                Some(DScope::Var(v, Kind::Type)) => Ok(self.arena.ty(Ty::Var(v))),
                Some(DScope::Rec(t)) => Ok(t),
                _ => Err(FxError::at(s.span, format!("`{}` is not a type", self.name(sym)))),
            };
        }
        let items = self.items(s, "a type")?.to_vec();
        if let Some(head) = items.first().and_then(|h| h.as_symbol())
            && let Some(DScope::Abbrev { params, body }) = self.lookup_desc(head)
        {
            return self.expand_abbrev(s, head, &params, &body, &items[1..]);
        }
        match self.head(&items).unwrap_or("") {
            "subr" => {
                let [_, effect, params, result] = &items[..] else {
                    return Err(FxError::at(s.span, "`(subr effect (param …) result)`"));
                };
                let effect = self.parse_effect(effect)?;
                let params = match &params.datum {
                    Datum::Nil => Vec::new(),
                    _ => self
                        .items(params, "parameter types")?
                        .to_vec()
                        .iter()
                        .map(|p| self.parse_type(p))
                        .collect::<R<Vec<_>>>()?,
                };
                let result = self.parse_type(result)?;
                Ok(self.arena.ty(Ty::Subr { effect, params, result }))
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
                Ok(self.arena.ty(Ty::Pair(a, b, r)))
            }
            "dletrec" => self.parse_dletrec(s, &items),
            "listof" => {
                // FX-87's `listof`: a pair whose tail is the list itself.
                // Every `pairof` type also has the empty list, `nil`.
                let [_, t, r] = &items[..] else {
                    return Err(FxError::at(s.span, "`(listof type region)`"));
                };
                let t = self.parse_type(t)?;
                let r = self.parse_region(r)?;
                let slot = self.arena.ty(Ty::Link(None));
                let pair = self.arena.ty(Ty::Pair(t, slot, r));
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
            "composable" => {
                let [_, t, a, d, r] = &items[..] else {
                    return Err(FxError::at(s.span, "`(composable argument answer effect region)`"));
                };
                let arg = self.parse_type(t)?;
                let answer = self.parse_type(a)?;
                let effect = self.parse_effect(d)?;
                let region = self.parse_region(r)?;
                Ok(self.arena.ty(Ty::Composable { arg, answer, effect, region }))
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
            "arrayof" => {
                let [_, t, r] = &items[..] else {
                    return Err(FxError::at(s.span, "`(arrayof type region)`"));
                };
                let t = self.parse_type(t)?;
                let r = self.parse_region(r)?;
                Ok(self.arena.ty(Ty::Array(t, r)))
            }
            "mark-key" => {
                let [_, t, r] = &items[..] else {
                    return Err(FxError::at(s.span, "`(mark-key type region)`"));
                };
                let t = self.parse_type(t)?;
                let r = self.parse_region(r)?;
                Ok(self.arena.ty(Ty::MarkKey(t, r)))
            }
            _ => Err(FxError::at(s.span, "expected a type")),
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
            self.parse_type(body)
        })();
        self.dscope.truncate(depth);
        result
    }

    /// A name defined as another name, round a loop, describes nothing.
    fn grounded(&self, slot: TyId, span: fixpt_read::Span) -> R<()> {
        let mut seen = std::collections::HashSet::new();
        let mut id = slot;
        while let Ty::Link(Some(next)) = self.arena.get_raw(id) {
            if !seen.insert(id) {
                return Err(FxError::at(span, "a recursive type must be built from a constructor, not only from names"));
            }
            id = *next;
        }
        Ok(())
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

    /// A use of a parametric abbreviation: its body, parsed with each
    /// parameter bound to the description given for it.
    fn expand_abbrev(&mut self, s: &Syntax, name: Sym, params: &[(Sym, Kind)], body: &Syntax, args: &[Syntax]) -> R<TyId> {
        if args.len() != params.len() {
            return Err(FxError::at(s.span, format!("`{}` takes {} description(s), and has {}", self.name(name), params.len(), args.len())));
        }
        if self.expanding > 64 {
            return Err(FxError::at(s.span, format!("`{}` expands without end: an abbreviation with parameters cannot mention itself", self.name(name))));
        }
        let mut bound = Vec::new();
        for ((p, k), a) in params.iter().zip(args) {
            let d = match k {
                Kind::Type => DScope::Rec(self.parse_type(a)?),
                Kind::Region => DScope::Region(self.parse_region(a)?),
                Kind::Place => DScope::Region(self.parse_place(a)?),
                Kind::Effect => DScope::Eff(self.parse_effect(a)?),
            };
            bound.push((*p, d));
        }
        let depth = self.dscope.len();
        self.dscope.extend(bound);
        self.expanding += 1;
        let r = self.parse_type(body);
        self.expanding -= 1;
        self.dscope.truncate(depth);
        r
    }

    /// `(define-type name type)`: `name` stands for the type from here on,
    /// and may appear in its own definition — a one-binding `dletrec` that
    /// stays in scope.
    pub(crate) fn define_type(&mut self, name: Sym, def: &Syntax, span: fixpt_read::Span) -> R<TyId> {
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
        r.map(|()| slot)
    }

    /// A `proj` argument. Which kind it is shows in its shape — `@x` is a
    /// region, `pure` and `(read …)`, `(maxeff …)` and the like are effects —
    /// or, for a bare name, in how the name is bound; the checker confirms it
    /// against the binder when it sees the `poly` being projected.
    fn parse_d(&mut self, s: &Syntax) -> R<D> {
        if let Some(sym) = s.as_symbol() {
            let name = self.name(sym);
            if name.starts_with('@') {
                return Ok(D::Region(self.region_constant(sym)));
            }
            if name == "pure" {
                return Ok(D::Effect(Effect::pure()));
            }
            return match self.lookup_desc(sym) {
                Some(DScope::Var(v, Kind::Region | Kind::Place)) => Ok(D::Region(Region::Var(v))),
                Some(DScope::Var(v, Kind::Effect)) => Ok(D::Effect(Effect::atom(Atom::Var(v)))),
                Some(DScope::Eff(e)) => Ok(D::Effect(e)),
                _ => Ok(D::Type(self.parse_type(s)?)),
            };
        }
        let items = self.items(s, "a description")?;
        match self.head(items).unwrap_or("") {
            "read" | "write" | "alloc" | "goto" | "comefrom" | "maxeff" => {
                Ok(D::Effect(self.parse_effect(s)?))
            }
            _ => Ok(D::Type(self.parse_type(s)?)),
        }
    }

    // ---------------------------------------------------------- expressions
    pub fn parse_exp(&mut self, s: &Syntax) -> R<ExpId> {
        let span = s.span;
        match &s.datum {
            Datum::Number(fixpt_read::Num::Int(n)) => return Ok(self.arena.exp(span, Exp::Int(*n))),
            Datum::Str(t) => return Ok(self.arena.exp(span, Exp::Str(t.clone()))),
            Datum::Bool(b) => return Ok(self.arena.exp(span, Exp::Bool(*b))),
            Datum::Char(c) => return Ok(self.arena.exp(span, Exp::Char(*c))),
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
        let items = self.items(s, "an expression")?.to_vec();
        match self.head(&items).unwrap_or("") {
            "lambda" => {
                let [_, params, body @ ..] = &items[..] else {
                    return Err(FxError::at(span, "`(lambda ((name type) …) body …)`"));
                };
                self.parse_lambda(span, params, body)
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
                let depth = self.dscope.len();
                let parsed = self
                    .parse_binders(binders)
                    .and_then(|b| Ok((b, self.parse_body(span, body)?)));
                self.dscope.truncate(depth);
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
                for b in self.items(bindings, "letrec bindings")?.to_vec() {
                    let parts = self.items(&b, "a letrec binding")?.to_vec();
                    let [name, ty, init] = &parts[..] else {
                        return Err(FxError::at(b.span, "a letrec binding is `(name type expression)`"));
                    };
                    let name = name.as_symbol().ok_or_else(|| FxError::at(name.span, "a name"))?;
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
                    Datum::Nil => Vec::new(),
                    _ => self.items(bindings, "let bindings")?.to_vec(),
                };
                for b in bs {
                    let parts = self.items(&b, "a let binding")?.to_vec();
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
            "cond" => self.parse_cond(span, &items[1..]),
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
                    Datum::Nil => Vec::new(),
                    _ => self.items(bindings, "let* bindings")?.to_vec(),
                };
                let mut parsed = Vec::new();
                for b in &bs {
                    let parts = self.items(b, "a let* binding")?.to_vec();
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
            name if BlobletOp::NAMES.contains(&name) => {
                let name = name.to_string();
                self.parse_bloblet(span, &name, &items[1..])
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
                _ => Err(FxError::at(span, "only a symbol can be quoted: `'name`")),
            },
            form @ ("letregion" | "letrena" | "letreap") => {
                let [_, name, body @ ..] = &items[..] else {
                    return Err(FxError::at(span, format!("`({form} name body …)`")));
                };
                let name = name.as_symbol().filter(|n| !self.name(*n).starts_with('@')).ok_or_else(|| {
                    FxError::at(name.span, format!("a `{form}` binds a region variable's name, without `@`"))
                })?;
                let form = match form {
                    "letregion" => RegionForm::Region,
                    "letrena" => RegionForm::Arena,
                    _ => RegionForm::Reap,
                };
                let depth = self.dscope.len();
                // `letrena` and `letreap` make a place (which is also a
                // region), `letregion` a region only.
                let kind = if form == RegionForm::Region { Kind::Region } else { Kind::Place };
                let region = self.arena.dvar_of(name, kind);
                self.dscope.push((name, DScope::Var(region, kind)));
                let body = self.parse_body(span, body);
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

    /// A label or tag: a symbol, or a positive integer, as FX-91's
    /// `define-datatype` numbers a variant's members.
    fn label(&mut self, s: &Syntax) -> R<Sym> {
        if let Some(x) = s.as_symbol() {
            return Ok(x);
        }
        match self.literal_int(s) {
            Some(n) if n > 0 => Ok(self.interner.intern(&n.to_string())),
            _ => Err(FxError::at(s.span, "a label is a name or a positive integer")),
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
            _ => {
                let shape = match name {
                    "make-bloblet" => "(make-bloblet bytes field …)",
                    "rmake-bloblet" => "(rmake-bloblet region bytes field …)",
                    "bloblet-ref" => "(bloblet-ref bloblet index)",
                    "bloblet-set!" => "(bloblet-set! bloblet index value)",
                    "bloblet-freeze" => "(bloblet-freeze bloblet)",
                    "bloblet-byte" => "(bloblet-byte bloblet i)",
                    "bloblet-set-byte!" => "(bloblet-set-byte! bloblet i byte)",
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
