//! Syntax to the kernel.
//!
//! The surface is FX-87's (`docs/fx26.md`, "The kernel"): n-ary forms, binder
//! lists in parentheses — `(plambda ((t type)) …)` — and `@name` for a region
//! constant. `let` and `begin` are derived forms, and `lambda` and `letrec`
//! bodies are implicit `begin`s.

use crate::ast::{Atom, D, DVar, Effect, Exp, ExpId, Kind, Region, Ty, TyId};
use crate::check::Checker;
use crate::error::{FxError, R};
use fixpt_read::{Datum, Sym, Syntax};

/// What a description name means where it is used.
#[derive(Copy, Clone, Debug)]
pub enum DScope {
    Var(DVar, Kind),
    /// A name bound by `dletrec`: a type.
    Rec(TyId),
}

impl Checker {
    fn name(&self, s: Sym) -> &str {
        self.interner.name(s)
    }

    fn lookup_desc(&self, s: Sym) -> Option<DScope> {
        self.dscope.iter().rev().find(|(n, _)| *n == s).map(|(_, d)| *d)
    }

    fn items<'s>(&self, s: &'s Syntax, what: &str) -> R<&'s [Syntax]> {
        s.as_proper_list().ok_or_else(|| FxError::at(s.span, format!("{what}: expected a list")))
    }

    fn head(&self, items: &[Syntax]) -> Option<&str> {
        items.first().and_then(|h| h.as_symbol()).map(|h| self.name(h))
    }

    // --------------------------------------------------------------- kinds
    fn parse_kind(&self, s: &Syntax) -> R<Kind> {
        match s.as_symbol().map(|k| self.name(k)) {
            Some("region") => Ok(Kind::Region),
            Some("effect") => Ok(Kind::Effect),
            Some("type") => Ok(Kind::Type),
            _ => Err(FxError::at(s.span, "a kind is `region`, `effect` or `type`")),
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
            let v = self.arena.dvar(name);
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
            return Ok(Region::Const(sym));
        }
        match self.lookup_desc(sym) {
            Some(DScope::Var(v, Kind::Region)) => Ok(Region::Var(v)),
            _ => Err(FxError::at(s.span, format!("`{}` is not a region", self.name(sym)))),
        }
    }

    // ------------------------------------------------------------- effects
    pub(crate) fn parse_effect(&self, s: &Syntax) -> R<Effect> {
        if let Some(sym) = s.as_symbol() {
            if self.name(sym) == "pure" {
                return Ok(Effect::pure());
            }
            return match self.lookup_desc(sym) {
                Some(DScope::Var(v, Kind::Effect)) => Ok(Effect::atom(Atom::Var(v))),
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
            // A name defined as another name, round a loop, describes nothing.
            for (slot, _) in &slots {
                let mut seen = std::collections::HashSet::new();
                let mut id = *slot;
                while let Ty::Link(Some(next)) = self.arena.get_raw(id) {
                    if !seen.insert(id) {
                        return Err(FxError::at(s.span, "a `dletrec` type must be built from a constructor, not only from names"));
                    }
                    id = *next;
                }
            }
            self.parse_type(body)
        })();
        self.dscope.truncate(depth);
        result
    }

    /// A `proj` argument. Which kind it is shows in its shape — `@x` is a
    /// region, `pure` and `(read …)`, `(maxeff …)` and the like are effects —
    /// or, for a bare name, in how the name is bound; the checker confirms it
    /// against the binder when it sees the `poly` being projected.
    fn parse_d(&mut self, s: &Syntax) -> R<D> {
        if let Some(sym) = s.as_symbol() {
            let name = self.name(sym);
            if name.starts_with('@') {
                return Ok(D::Region(Region::Const(sym)));
            }
            if name == "pure" {
                return Ok(D::Effect(Effect::pure()));
            }
            return match self.lookup_desc(sym) {
                Some(DScope::Var(v, Kind::Region)) => Ok(D::Region(Region::Var(v))),
                Some(DScope::Var(v, Kind::Effect)) => Ok(D::Effect(Effect::atom(Atom::Var(v)))),
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
            Datum::Symbol(sym) => {
                // FX-87's reader delivers `#t`, `#f` and `#u` as symbols.
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
                let params = match &params.datum {
                    Datum::Nil => Vec::new(),
                    _ => self
                        .items(params, "parameters")?
                        .to_vec()
                        .iter()
                        .map(|p| {
                            let pair = self.items(p, "a parameter")?.to_vec();
                            let [name, ty] = &pair[..] else {
                                return Err(FxError::at(p.span, "a parameter is `(name type)`"));
                            };
                            let name = name.as_symbol().ok_or_else(|| FxError::at(name.span, "a name"))?;
                            Ok((name, self.parse_type(ty)?))
                        })
                        .collect::<R<Vec<_>>>()?,
                };
                let body = self.parse_body(span, body)?;
                Ok(self.arena.exp(span, Exp::Lambda { params, body }))
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
            _ => {
                let fun = self.parse_exp(&items[0])?;
                let args = items[1..].iter().map(|a| self.parse_exp(a)).collect::<R<Vec<_>>>()?;
                Ok(self.arena.exp(span, Exp::App { fun, args }))
            }
        }
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
