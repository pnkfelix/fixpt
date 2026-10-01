//! Syntax to the kernel.
//!
//! The forms are FX-87's (`docs/fx26.md`, "The kernel"): n-ary forms, binder
//! lists in parentheses — `(plambda ((t type)) …)` — and `@name` for a region
//! constant. The lexical syntax is FX-26's own, `SyntaxProfile::FX26`. `let` and `begin` are derived forms, and `lambda` and `letrec`
//! bodies are implicit `begin`s. A `lambda` parameter may be a bare name, when
//! the `lambda` is checked against a type that says what it is.

use crate::ast::{Arm, ArmBind, Atom, BlobletOp, Conv, D, DVar, Effect, Exp, ExpId, Kind, Region, RegionForm, Size, Ty, TyId, Variance};
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
    /// A region constant `private-regions` made the program's own: `@s` in
    /// the program is this fresh region, which nothing else can name.
    Private(Region),
}

/// A description given a type family, as a key for its knot.
#[derive(Clone, PartialEq, Debug)]
pub enum FamilyArg {
    Ty(TyId),
    Region(Region),
    Eff(crate::ast::Effect),
    Size(Size),
    Conv(Conv),
}

impl Checker {
    fn name(&self, s: Sym) -> &str {
        self.interner.name(s)
    }

    /// The region `@name` stands for: the program's own, if `private-regions`
    /// declared it, and otherwise the constant of that name.
    pub(crate) fn region_constant(&self, sym: Sym) -> Region {
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
            Some("data") => Ok(Kind::Data),
            Some("size") => Ok(Kind::Size),
            Some("conv") => Ok(Kind::Conv),
            _ => Err(FxError::at(s.span, "a kind is `region`, `place`, `effect`, `type`, `data`, `size` or `conv`")),
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
    fn parse_binders(&mut self, s: &Syntax) -> R<Vec<(DVar, Kind)>> {
        let mut out = Vec::new();
        for b in self.items(s, "binders")? {
            let pair = self.items(b, "a binder")?;
            let (name, kind, bound) = match pair {
                [name, kind] => (name, kind, None),
                [name, kind, bound] => (name, kind, Some(bound)),
                _ => return Err(FxError::at(b.span, "a binder is `(name kind)`, `(name region place)` or `(name data place)`")),
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
            let v = self.arena.dvar_of(name, kind);
            if let Some(p) = bound {
                self.arena.set_bound(v, p);
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

    // ------------------------------------------------------------- effects
    pub(crate) fn parse_effect(&self, s: &Syntax) -> R<Effect> {
        if let Some(sym) = s.as_symbol() {
            if self.name(sym) == "pure" {
                return Ok(Effect::pure());
            }
            if self.name(sym) == "spin" {
                return Ok(Effect::atom(Atom::Spin));
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
        let t = self.parse_type_node(s)?;
        // Storage written: a procedure kept there may not reach itself
        // unsaid (`spin`).
        if matches!(self.head(self.items(s, "a type").unwrap_or(&[])), Some("ref" | "icell" | "pairof" | "listof" | "bloblet" | "arrayof" | "mark-key" | "mu")) {
            self.no_knot(t, s.span)?;
        }
        Ok(t)
    }

    fn parse_type_node(&mut self, s: &Syntax) -> R<TyId> {
        if let Some(sym) = s.as_symbol() {
            let name = self.name(sym);
            if name == "void" {
                return Ok(self.void);
            }
            if name == "nat" && self.lookup_desc(sym).is_none() {
                return Ok(self.arena.ty(Ty::Nat(Size::Finite)));
            }
            if let Some(&t) = self.base.get(&sym) {
                return Ok(t);
            }
            return match self.lookup_desc(sym) {
                Some(DScope::Var(v, Kind::Type | Kind::Data)) => Ok(self.arena.ty(Ty::Var(v))),
                Some(DScope::Rec(t)) => Ok(t),
                Some(DScope::Generative(g)) => self.apply_generative(s, g, &[]),
                _ if self.holes.is_some_and(|h| h.exp == sym) => Err(FxError::at(s.span, "expected a type")),
                _ => Err(FxError::at(s.span, format!("`{}` is not a type", self.name(sym)))),
            };
        }
        let items = self.items(s, "a type")?.to_vec();
        if let Some(head) = items.first().and_then(|h| h.as_symbol()) {
            match self.lookup_desc(head) {
                Some(DScope::Abbrev { params, body }) => return self.expand_abbrev(s, head, &params, &body, &items[1..]),
                Some(DScope::Generative(g)) => return self.apply_generative(s, g, &items[1..]),
                _ => {}
            }
        }
        match self.head(&items).unwrap_or("") {
            // `(subr effect (param …) result)`, or with a convention first,
            // `(subr (conv C) effect (param …) result)`; left out, it is the
            // program's (`docs/research/native-conventions.md`).
            "subr" => {
                let (conv, rest) = match &items[..] {
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
                Ok(self.arena.ty(Ty::Subr { conv, effect, params, result }))
            }
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
                Ok(self.arena.ty(Ty::Pair(a, b, r)))
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
            for (slot, _) in &slots {
                self.no_knot(*slot, s.span)?;
            }
            self.parse_type(body)
        })();
        self.dscope.truncate(depth);
        result
    }

    /// A name defined as another name, round a loop, describes nothing.
    pub(crate) fn grounded(&self, slot: TyId, span: fixpt_read::Span) -> R<()> {
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
                Kind::Type | Kind::Data => {
                    let t = self.parse_type(a)?;
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
            hs.iter().map(|(x, y)| self.arena.ty(Ty::Subr { conv: self.conv_default, effect: spin.clone(), params: vec![*x], result: *y })).collect();
        params.push(lhs);
        let body = self.arena.ty(Ty::Subr { conv: self.conv_default, effect: spin, params, result: rhs });
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
                Kind::Type | Kind::Data => D::Type(self.parse_type(a)?),
                Kind::Region => D::Region(self.parse_region(a)?),
                Kind::Place => D::Region(self.parse_place(a)?),
                Kind::Effect => D::Effect(self.parse_effect(a)?),
                Kind::Size => D::Size(self.parse_size(a)?),
                Kind::Conv => D::Conv(self.parse_conv(a)?),
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
        r.map(|()| slot)
    }

    /// A `proj` argument. Which kind it is shows in its shape — `@x` is a
    /// region, `pure` and `(read …)`, `(maxeff …)` and the like are effects —
    /// or, for a bare name, in how the name is bound; the checker confirms it
    /// against the binder when it sees the `poly` being projected.
    fn parse_d(&mut self, s: &Syntax) -> R<D> {
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
                Some(DScope::Var(v, Kind::Region | Kind::Place)) => Ok(D::Region(Region::Var(v))),
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
            "const" | "acyclic" => Ok(D::Region(self.parse_region(s)?)),
            "+" | "-" => Ok(D::Size(self.parse_size(s)?)),
            "read" | "write" | "alloc" | "goto" | "comefrom" | "maxeff" => {
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
        let items = self.items(s, "an expression")?.to_vec();
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
                let var = |c: &mut Checker, n: &str| {
                    let s = c.interner.intern(n);
                    c.arena.exp(span, Exp::Var(s))
                };
                let tmp = self.interner.intern("%confirm-value");
                let (f, a, l) = (var(self, "length-is?"), var(self, "%confirm-value"), self.arena.exp(span, k.clone()));
                let test = self.arena.exp(span, Exp::App { fun: f, args: vec![a, l] });
                let (f, a, l) = (var(self, "certify-length"), var(self, "%confirm-value"), self.arena.exp(span, k));
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
                let var = |c: &mut Checker, n: &str| {
                    let s = c.interner.intern(n);
                    c.arena.exp(span, Exp::Var(s))
                };
                let tmp = self.interner.intern("%acyclic-value");
                let (test_f, test_a) = (var(self, "acyclic?"), var(self, "%acyclic-value"));
                let test = self.arena.exp(span, Exp::App { fun: test_f, args: vec![test_a] });
                let (cert_f, cert_a) = (var(self, "certify-acyclic"), var(self, "%acyclic-value"));
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
                let var = |c: &mut Checker, n: &str| {
                    let s = c.interner.intern(n);
                    c.arena.exp(span, Exp::Var(s))
                };
                let tmp = self.interner.intern("%nat-value");
                let (test_f, test_a) = (var(self, "nat?"), var(self, "%nat-value"));
                let test = self.arena.exp(span, Exp::App { fun: test_f, args: vec![test_a] });
                let (cert_f, cert_a) = (var(self, "certify-nat"), var(self, "%nat-value"));
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
                _ => Err(FxError::at(span, "only a symbol can be quoted: `'name`")),
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
