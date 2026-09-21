//! Reading FX-87 source into the arena.
//!
//! Two languages in one file, because the grammar interleaves them: a `lambda`
//! parameter carries a *description*, and a description can be applied to
//! others. `syntax.lisp` splits the job the same way.
//!
//! # Bound variables decide what a bare name means
//!
//! `t` is a description variable inside `(poly ((t type)) …)` and the name of a
//! standard constructor outside it. Nothing about the token says which, so the
//! parser carries the set of description variables currently in scope: bound
//! names become [`Desc::Var`], unbound ones [`Desc::Con`]. The reference does
//! exactly this with its `alpha-env`.
//!
//! # Sugar
//!
//! `let`, `let*`, `and`, `or`, `cond` and `do` are expanded here rather than
//! given nodes of their own, as `sugar.lisp` does — so the checker sees only
//! the kernel, and there is one place to look when a derived form is wrong.

use crate::ast::{
    Arena, Binder, Binding, Desc, DescId, DoBinding, Exp, ExpId, Kind, Param, TagClause,
};
use crate::error::{FxError, R};
use crate::syms::Syms;
use fixpt_read::{Datum, Interner, Num, Span, Sym, Syntax};

/// What a bare name means while a description is being read.
///
/// `bound` are the variables in scope, which become [`Desc::Var`]; anything
/// else is a standard constructor. `subst` is for the binding forms that give a
/// name a *description* rather than a variable — `dlet`, and `dletrec`, whose
/// names resolve to the holes being tied. Keeping both in one place is what
/// lets every description form nest inside every other.
#[derive(Clone, Default)]
pub struct DScope {
    pub bound: Vec<Sym>,
    pub subst: std::collections::HashMap<Sym, DescId>,
}

impl DScope {
    pub fn with(&self, names: &[Sym]) -> DScope {
        let mut next = self.clone();
        next.bound.extend_from_slice(names);
        next
    }

    fn lookup(&self, s: Sym) -> Option<DescId> {
        self.subst.get(&s).copied()
    }
}

pub struct Parser {
    pub arena: Arena,
    pub interner: Interner,
    pub syms: Syms,
}

impl Parser {
    pub fn new() -> Parser {
        let mut interner = Interner::new();
        let syms = Syms::new(&mut interner);
        Parser { arena: Arena::new(), interner, syms }
    }

    // ------------------------------------------------------------ helpers
    fn list<'a>(&self, s: &'a Syntax) -> Option<&'a [Syntax]> {
        match &s.datum {
            Datum::List { items, tail } if tail.is_none() => Some(items),
            // `()` is the empty list, which matters for `(lambda () …)`.
            Datum::Nil => Some(&[]),
            _ => None,
        }
    }

    fn sym_of(&self, s: &Syntax) -> Option<Sym> {
        match &s.datum {
            Datum::Symbol(sym) => Some(*sym),
            _ => None,
        }
    }

    /// The head symbol of a list, if it has one.
    fn head(&self, s: &Syntax) -> Option<Sym> {
        self.list(s).and_then(|items| items.first()).and_then(|h| self.sym_of(h))
    }

    fn bad(&self, s: &Syntax, what: &str) -> FxError {
        FxError::syntax(s.span, format!("malformed {what}"))
    }

    // ------------------------------------------------------------- kinds
    pub fn parse_kind(&mut self, s: &Syntax) -> R<Kind> {
        if let Some(sym) = self.sym_of(s) {
            if sym == self.syms.kind_type {
                return Ok(Kind::Type);
            }
            if sym == self.syms.kind_effect {
                return Ok(Kind::Effect);
            }
            if sym == self.syms.kind_region {
                return Ok(Kind::Region);
            }
        }
        // `(dfunc (k…) k)`
        if let (Some(h), Some(items)) = (self.head(s), self.list(s))
            && h == self.syms.dfunc
            && items.len() == 3
        {
            let args = self.list(&items[1]).ok_or_else(|| self.bad(s, "dfunc kind"))?.to_vec();
            let args: R<Vec<Kind>> = args.iter().map(|a| self.parse_kind(a)).collect();
            let result = self.parse_kind(&items[2])?;
            return Ok(Kind::DFunc(args?, Box::new(result)));
        }
        Err(self.bad(s, "kind"))
    }

    /// `((v kind) …)`
    fn parse_binders(&mut self, s: &Syntax, bound: &mut Vec<Sym>) -> R<Vec<Binder>> {
        let items = self.list(s).ok_or_else(|| self.bad(s, "binder list"))?.to_vec();
        let mut out = Vec::with_capacity(items.len());
        for item in &items {
            let parts = self.list(item).ok_or_else(|| self.bad(item, "binder"))?.to_vec();
            if parts.len() != 2 {
                return Err(self.bad(item, "binder"));
            }
            let name = self.sym_of(&parts[0]).ok_or_else(|| self.bad(item, "binder name"))?;
            let kind = self.parse_kind(&parts[1])?;
            bound.push(name);
            out.push(Binder { name, kind });
        }
        Ok(out)
    }

    // ------------------------------------------------------ descriptions
    pub fn parse_desc(&mut self, s: &Syntax, scope: &DScope) -> R<DescId> {
        if let Some(sym) = self.sym_of(s) {
            // A name bound by `dlet` or `dletrec` *is* its description.
            if let Some(id) = scope.lookup(sym) {
                return Ok(id);
            }
            if sym == self.syms.pure {
                return Ok(self.arena.desc(Desc::Pure));
            }
            return Ok(if scope.bound.contains(&sym) {
                self.arena.desc(Desc::Var(sym))
            } else {
                self.arena.con0(sym)
            });
        }
        let items = self.list(s).ok_or_else(|| self.bad(s, "description"))?.to_vec();
        if items.is_empty() {
            return Err(self.bad(s, "description"));
        }
        let Some(h) = self.sym_of(&items[0]) else {
            // The head is itself a description — an inline `dlambda` being
            // applied, as in `((dlambda ((t type)) t) int)`.
            let fun = self.parse_desc(&items[0], scope)?;
            let args = self.parse_desc_seq(&items[1..], scope)?;
            return Ok(self.arena.desc(Desc::DApp { fun, args }));
        };
        let a = items[1..].to_vec();

        if h == self.syms.subr {
            if a.len() != 3 {
                return Err(self.bad(s, "subr"));
            }
            let effect = self.parse_desc(&a[0], scope)?;
            let args = self.parse_desc_list(&a[1], scope)?;
            let result = self.parse_desc(&a[2], scope)?;
            return Ok(self.arena.desc(Desc::Subr { effect, args, result }));
        }
        if h == self.syms.vsubr {
            if a.len() < 3 {
                return Err(self.bad(s, "vsubr"));
            }
            let effect = self.parse_desc(&a[0], scope)?;
            let mut parts = Vec::new();
            for item in &a[1..] {
                parts.push(self.parse_desc(item, scope)?);
            }
            let result = parts.pop().expect("checked length");
            let rest = parts.pop().expect("checked length");
            return Ok(self.arena.desc(Desc::Vsubr { effect, args: parts, rest, result }));
        }
        if h == self.syms.poly || h == self.syms.dlambda {
            if a.len() != 2 {
                return Err(self.bad(s, "poly"));
            }
            let mut names = Vec::new();
            let binders = self.parse_binders(&a[0], &mut names)?;
            let inner = scope.with(&names);
            let body = self.parse_desc(&a[1], &inner)?;
            return Ok(self.arena.desc(if h == self.syms.poly {
                Desc::Poly { binders, body }
            } else {
                Desc::DAbs { binders, body }
            }));
        }
        if h == self.syms.recordof || h == self.syms.oneof {
            if a.len() != 2 {
                return Err(self.bad(s, "recordof/oneof"));
            }
            let fields = self.parse_fields(&a[0], scope)?;
            let region = self.parse_desc(&a[1], scope)?;
            return Ok(self.arena.desc(if h == self.syms.recordof {
                Desc::RecordOf { fields, region }
            } else {
                Desc::OneOf { variants: fields, region }
            }));
        }
        if h == self.syms.dlet {
            // `(dlet ((v d)…) body)` — non-recursive, so the right-hand sides
            // are read in the *outer* scope.
            if a.len() != 2 {
                return Err(self.bad(s, "dlet"));
            }
            let pairs = self.list(&a[0]).ok_or_else(|| self.bad(s, "dlet bindings"))?.to_vec();
            let mut inner = scope.clone();
            for pair in &pairs {
                let parts = self.list(pair).ok_or_else(|| self.bad(pair, "dlet binding"))?.to_vec();
                if parts.len() != 2 {
                    return Err(self.bad(pair, "dlet binding"));
                }
                let name = self.sym_of(&parts[0]).ok_or_else(|| self.bad(pair, "dlet name"))?;
                let value = self.parse_desc(&parts[1], scope)?;
                inner.subst.insert(name, value);
            }
            return self.parse_desc(&a[1], &inner);
        }
        if h == self.syms.dletrec {
            return self.parse_dletrec(s, &items, scope);
        }
        if h == self.syms.read || h == self.syms.write || h == self.syms.alloc {
            if a.len() != 1 {
                return Err(self.bad(s, "effect"));
            }
            let r = self.parse_desc(&a[0], scope)?;
            return Ok(self.arena.desc(if h == self.syms.read {
                Desc::Read(r)
            } else if h == self.syms.write {
                Desc::Write(r)
            } else {
                Desc::Alloc(r)
            }));
        }
        if h == self.syms.maxeff {
            let parts = self.parse_desc_seq(&a, scope)?;
            return Ok(self.arena.maxeff(parts));
        }
        if h == self.syms.runion {
            // `eval-rexp` flattens a written union with a right fold that
            // prepends, so its members end up reversed — `(runion @red @blue)`
            // written in an ascription is reported as `(runion @blue @red)`.
            // Reversing here rather than during evaluation matters: masking
            // rebuilds effects, so an evaluation-time reversal would be applied
            // a varying number of times, while a union is *written* once.
            let mut parts = self.parse_desc_seq(&a, scope)?;
            parts.reverse();
            return Ok(self.arena.runion(parts));
        }

        let args = self.parse_desc_seq(&a, scope)?;
        if let Some(id) = scope.lookup(h) {
            return Ok(self.arena.desc(Desc::DApp { fun: id, args }));
        }
        if scope.bound.contains(&h) {
            let fun = self.arena.desc(Desc::Var(h));
            return Ok(self.arena.desc(Desc::DApp { fun, args }));
        }
        Ok(self.arena.desc(Desc::Con(h, args)))
    }

    /// `(dletrec ((v d)…) body)` — recursive descriptions, written by hand.
    ///
    /// Every name is bound to a hole first, so a body may refer to any of them
    /// including itself; the holes are filled once all the bodies exist. This is
    /// the same knot the checker ties when it builds a list type, which is why
    /// one printer handles both.
    fn parse_dletrec(&mut self, s: &Syntax, items: &[Syntax], scope: &DScope) -> R<DescId> {
        if items.len() != 3 {
            return Err(self.bad(s, "dletrec"));
        }
        let bindings =
            self.list(&items[1]).ok_or_else(|| self.bad(s, "dletrec bindings"))?.to_vec();
        let mut inner = scope.clone();
        let mut names = Vec::with_capacity(bindings.len());
        for b in &bindings {
            let parts = self.list(b).ok_or_else(|| self.bad(b, "dletrec binding"))?.to_vec();
            if parts.len() != 2 {
                return Err(self.bad(b, "dletrec binding"));
            }
            let name = self.sym_of(&parts[0]).ok_or_else(|| self.bad(b, "dletrec name"))?;
            let hole = self.arena.hole();
            inner.subst.insert(name, hole);
            names.push((name, hole, parts[1].clone()));
        }
        for (_, hole, syntax) in &names {
            let built = self.parse_desc(syntax, &inner)?;
            let contents = self.arena.get(built).clone();
            self.arena.fill(*hole, contents);
        }
        self.parse_desc(&items[2], &inner)
    }

    fn parse_desc_list(&mut self, s: &Syntax, scope: &DScope) -> R<Vec<DescId>> {
        let items = self.list(s).ok_or_else(|| self.bad(s, "description list"))?.to_vec();
        self.parse_desc_seq(&items, scope)
    }

    fn parse_desc_seq(&mut self, items: &[Syntax], scope: &DScope) -> R<Vec<DescId>> {
        let mut out = Vec::with_capacity(items.len());
        for item in items {
            out.push(self.parse_desc(item, scope)?);
        }
        Ok(out)
    }

    fn parse_fields(&mut self, s: &Syntax, scope: &DScope) -> R<Vec<(Sym, DescId)>> {
        let items = self.list(s).ok_or_else(|| self.bad(s, "field list"))?.to_vec();
        let mut out = Vec::with_capacity(items.len());
        for item in &items {
            let parts = self.list(item).ok_or_else(|| self.bad(item, "field"))?.to_vec();
            if parts.len() != 2 {
                return Err(self.bad(item, "field"));
            }
            let name = self.sym_of(&parts[0]).ok_or_else(|| self.bad(item, "field name"))?;
            out.push((name, self.parse_desc(&parts[1], scope)?));
        }
        Ok(out)
    }

    // ------------------------------------------------------- expressions
    pub fn parse_exp(&mut self, s: &Syntax, scope: &DScope) -> R<ExpId> {
        let id = self.parse_exp_inner(s, scope)?;
        // Every node keeps the form it was read from, so a checking failure can
        // quote it the way the reference does.
        self.arena.set_source(id, s.clone());
        Ok(id)
    }

    fn parse_exp_inner(&mut self, s: &Syntax, scope: &DScope) -> R<ExpId> {
        let span = s.span;
        match &s.datum {
            Datum::Number(n) => {
                let e = match n {
                    Num::Int(i) => Exp::Int(*i),
                    Num::Real(f) => Exp::Float(f.to_bits()),
                    other => {
                        return Err(FxError::syntax(
                            span,
                            format!("FX-87 has no literal for {other:?}"),
                        ));
                    }
                };
                Ok(self.arena.exp(span, e))
            }
            Datum::Char(c) => Ok(self.arena.exp(span, Exp::Char(*c))),
            Datum::Str(t) => Ok(self.arena.exp(span, Exp::Str(t.clone()))),
            Datum::Symbol(sym) => {
                // The FX-87 reader hands back `#t`, `#f` and `#u` as symbols,
                // so the literals are recognised here rather than by the reader.
                let e = if *sym == self.syms.true_ {
                    Exp::Bool(true)
                } else if *sym == self.syms.false_ {
                    Exp::Bool(false)
                } else if *sym == self.syms.unit {
                    Exp::Unit
                } else {
                    Exp::Var(*sym)
                };
                Ok(self.arena.exp(span, e))
            }
            Datum::List { .. } | Datum::Nil => self.parse_form(s, scope),
            _ => Err(self.bad(s, "expression")),
        }
    }

    fn parse_form(&mut self, s: &Syntax, scope: &DScope) -> R<ExpId> {
        let span = s.span;
        let items = self.list(s).ok_or_else(|| self.bad(s, "form"))?.to_vec();
        if items.is_empty() {
            return Err(self.bad(s, "empty form"));
        }
        let head = self.sym_of(&items[0]);
        let a = &items[1..];

        if let Some(h) = head {
            // `quote` is only half a form in FX-87. A quoted *symbol* — and
            // `'()`, which the port's NIL emulation delivers as one — is a
            // literal of type `symbol`. A quoted list is not: `quote` stays an
            // ordinary variable there, and the corpus records the resulting
            // "This variable has no type quote". See docs/divergences.md.
            if h == self.syms.quote
                && a.len() == 1
                && matches!(a[0].datum, Datum::Nil | Datum::Symbol(_))
            {
                return Ok(self.arena.exp(span, Exp::Quote(a[0].clone())));
            }
            if h == self.syms.the {
                // `(the effect type exp)` or `(the type exp)`
                let (effect, ty, body) = match a.len() {
                    3 => (
                        Some(self.parse_desc(&a[0], scope)?),
                        self.parse_desc(&a[1], scope)?,
                        &a[2],
                    ),
                    2 => (None, self.parse_desc(&a[0], scope)?, &a[1]),
                    _ => return Err(self.bad(s, "the")),
                };
                let body = self.parse_exp(body, scope)?;
                return Ok(self.arena.exp(span, Exp::The { effect, ty, body }));
            }
            if h == self.syms.if_ {
                if a.len() != 3 {
                    return Err(self.bad(s, "if"));
                }
                let test = self.parse_exp(&a[0], scope)?;
                let then = self.parse_exp(&a[1], scope)?;
                let els = self.parse_exp(&a[2], scope)?;
                return Ok(self.arena.exp(span, Exp::If { test, then, els }));
            }
            if h == self.syms.begin {
                let body = self.parse_exp_seq(a, scope)?;
                return Ok(self.arena.exp(span, Exp::Begin(body)));
            }
            if h == self.syms.lambda {
                if a.len() < 2 {
                    return Err(self.bad(s, "lambda"));
                }
                let params = self.parse_params(&a[0], scope)?;
                let body = self.parse_body(&a[1..], scope)?;
                return Ok(self.arena.exp(span, Exp::Lambda { params, body }));
            }
            if h == self.syms.letrec {
                if a.len() < 2 {
                    return Err(self.bad(s, "letrec"));
                }
                let pairs = self.list(&a[0]).ok_or_else(|| self.bad(s, "letrec"))?.to_vec();
                let mut bindings = Vec::with_capacity(pairs.len());
                for p in &pairs {
                    let parts = self.list(p).ok_or_else(|| self.bad(p, "binding"))?.to_vec();
                    if parts.len() != 2 {
                        return Err(self.bad(p, "binding"));
                    }
                    let name = self.sym_of(&parts[0]).ok_or_else(|| self.bad(p, "name"))?;
                    let value = self.parse_exp(&parts[1], scope)?;
                    bindings.push(Binding { name, value, region: None });
                }
                let body = self.parse_body(&a[1..], scope)?;
                return Ok(self.arena.exp(span, Exp::Letrec { bindings, body }));
            }
            if h == self.syms.plambda {
                if a.len() < 2 {
                    return Err(self.bad(s, "plambda"));
                }
                let mut names = Vec::new();
                let binders = self.parse_binders(&a[0], &mut names)?;
                let inner = scope.with(&names);
                let body = self.parse_body(&a[1..], &inner)?;
                return Ok(self.arena.exp(span, Exp::PLambda { binders, body }));
            }
            if h == self.syms.proj {
                if a.len() < 2 {
                    return Err(self.bad(s, "proj"));
                }
                let body = self.parse_exp(&a[0], scope)?;
                let args = self.parse_desc_seq(&a[1..], scope)?;
                return Ok(self.arena.exp(span, Exp::Proj { body, args }));
            }
            if h == self.syms.set_bang {
                if a.len() != 2 {
                    return Err(self.bad(s, "set!"));
                }
                let name = self.sym_of(&a[0]).ok_or_else(|| self.bad(s, "set! target"))?;
                let value = self.parse_exp(&a[1], scope)?;
                return Ok(self.arena.exp(span, Exp::SetBang { name, value }));
            }
            // ---- standard forms ----
            if h == self.syms.record {
                // `(record ((f e)…) [region])`
                if a.is_empty() {
                    return Err(self.bad(s, "record"));
                }
                let pairs = self.list(&a[0]).ok_or_else(|| self.bad(s, "record"))?.to_vec();
                let mut fields = Vec::with_capacity(pairs.len());
                for pair in &pairs {
                    let parts = self.list(pair).ok_or_else(|| self.bad(pair, "field"))?.to_vec();
                    if parts.len() != 2 {
                        return Err(self.bad(pair, "field"));
                    }
                    let name = self.sym_of(&parts[0]).ok_or_else(|| self.bad(pair, "field"))?;
                    fields.push((name, self.parse_exp(&parts[1], scope)?));
                }
                let region = match a.len() {
                    1 => None,
                    2 => Some(self.parse_desc(&a[1], scope)?),
                    _ => return Err(self.bad(s, "record")),
                };
                return Ok(self.arena.exp(span, Exp::Record { fields, region }));
            }
            if h == self.syms.select {
                if a.len() != 2 {
                    return Err(self.bad(s, "select"));
                }
                let rec = self.parse_exp(&a[0], scope)?;
                let field = self.sym_of(&a[1]).ok_or_else(|| self.bad(s, "select field"))?;
                return Ok(self.arena.exp(span, Exp::Select { rec, field }));
            }
            if h == self.syms.record_set {
                if a.len() != 3 {
                    return Err(self.bad(s, "record-set!"));
                }
                let rec = self.parse_exp(&a[0], scope)?;
                let field = self.sym_of(&a[1]).ok_or_else(|| self.bad(s, "field"))?;
                let value = self.parse_exp(&a[2], scope)?;
                return Ok(self.arena.exp(span, Exp::RecordSet { rec, field, value }));
            }
            if h == self.syms.one {
                if a.len() != 3 {
                    return Err(self.bad(s, "one"));
                }
                let ty = self.parse_desc(&a[0], scope)?;
                let tag = self.sym_of(&a[1]).ok_or_else(|| self.bad(s, "tag"))?;
                let value = self.parse_exp(&a[2], scope)?;
                return Ok(self.arena.exp(span, Exp::One { ty, tag, value }));
            }
            if h == self.syms.one_set {
                if a.len() != 3 {
                    return Err(self.bad(s, "one-set!"));
                }
                let target = self.parse_exp(&a[0], scope)?;
                let tag = self.sym_of(&a[1]).ok_or_else(|| self.bad(s, "tag"))?;
                let value = self.parse_exp(&a[2], scope)?;
                return Ok(self.arena.exp(span, Exp::OneSet { target, tag, value }));
            }
            if h == self.syms.tagcase {
                if a.len() < 2 {
                    return Err(self.bad(s, "tagcase"));
                }
                let binding = self.list(&a[0]).ok_or_else(|| self.bad(s, "tagcase"))?.to_vec();
                if binding.len() < 2 {
                    return Err(self.bad(s, "tagcase binding"));
                }
                let var = self.sym_of(&binding[0]).ok_or_else(|| self.bad(s, "tagcase var"))?;
                let scrutinee = self.parse_exp(&binding[1], scope)?;
                let region = match binding.len() {
                    2 => None,
                    3 => Some(self.parse_desc(&binding[2], scope)?),
                    _ => return Err(self.bad(s, "tagcase binding")),
                };
                let mut clauses = Vec::new();
                for clause in &a[1..] {
                    let parts =
                        self.list(clause).ok_or_else(|| self.bad(clause, "tagcase clause"))?.to_vec();
                    if parts.is_empty() {
                        return Err(self.bad(clause, "tagcase clause"));
                    }
                    let tag = self.sym_of(&parts[0]).ok_or_else(|| self.bad(clause, "tag"))?;
                    let tag = if tag == self.syms.else_ { None } else { Some(tag) };
                    let body = self.parse_body(&parts[1..], scope)?;
                    clauses.push(TagClause { tag, body });
                }
                return Ok(self.arena.exp(
                    span,
                    Exp::TagCase { var, scrutinee, region, clauses },
                ));
            }
            if h == self.syms.delay {
                if a.len() != 1 {
                    return Err(self.bad(s, "delay"));
                }
                let body = self.parse_exp(&a[0], scope)?;
                return Ok(self.arena.exp(span, Exp::Delay(body)));
            }
            if h == self.syms.vlambda {
                if a.len() < 2 {
                    return Err(self.bad(s, "vlambda"));
                }
                let arg = self.list(&a[0]).ok_or_else(|| self.bad(s, "vlambda arg"))?.to_vec();
                if arg.len() < 2 {
                    return Err(self.bad(s, "vlambda arg"));
                }
                let name = self.sym_of(&arg[0]).ok_or_else(|| self.bad(s, "vlambda name"))?;
                let ty = self.parse_desc(&arg[1], scope)?;
                let region = match arg.len() {
                    2 => None,
                    3 => Some(self.parse_desc(&arg[2], scope)?),
                    _ => return Err(self.bad(s, "vlambda arg")),
                };
                let body = self.parse_body(&a[1..], scope)?;
                return Ok(self.arena.exp(span, Exp::VLambda { name, ty, region, body }));
            }
            if h == self.syms.plet {
                // `(plet ((v d)…) body)` binds *description* variables to
                // descriptions, so it is handled by extending the scope rather
                // than by a node of its own — exactly as `dlet` is.
                if a.len() < 2 {
                    return Err(self.bad(s, "plet"));
                }
                let pairs = self.list(&a[0]).ok_or_else(|| self.bad(s, "plet"))?.to_vec();
                let mut inner = scope.clone();
                for pair in &pairs {
                    let parts = self.list(pair).ok_or_else(|| self.bad(pair, "plet binding"))?.to_vec();
                    if parts.len() != 2 {
                        return Err(self.bad(pair, "plet binding"));
                    }
                    let name = self.sym_of(&parts[0]).ok_or_else(|| self.bad(pair, "plet name"))?;
                    let value = self.parse_desc(&parts[1], scope)?;
                    inner.subst.insert(name, value);
                }
                return self.parse_body(&a[1..], &inner);
            }
            // ---- sugar ----
            if h == self.syms.let_ || h == self.syms.let_star {
                return self.expand_let(s, h == self.syms.let_star, a, scope);
            }
            if h == self.syms.and {
                return self.expand_and(span, a, scope);
            }
            if h == self.syms.or {
                return self.expand_or(span, a, scope);
            }
            if h == self.syms.cond {
                return self.expand_cond(span, a, scope);
            }
            if h == self.syms.do_ {
                if a.len() < 2 {
                    return Err(self.bad(s, "do"));
                }
                let inits = self.list(&a[0]).ok_or_else(|| self.bad(s, "do"))?.to_vec();
                let mut bindings = Vec::with_capacity(inits.len());
                for init in &inits {
                    let parts = self.list(init).ok_or_else(|| self.bad(init, "do binding"))?.to_vec();
                    if parts.len() < 2 || parts.len() > 4 {
                        return Err(self.bad(init, "do binding"));
                    }
                    let name = self.sym_of(&parts[0]).ok_or_else(|| self.bad(init, "do name"))?;
                    let value = self.parse_exp(&parts[1], scope)?;
                    let step = match parts.len() {
                        2 => None,
                        _ => Some(self.parse_exp(&parts[2], scope)?),
                    };
                    // A fourth element names the region, as it does everywhere
                    // else a binding can be mutable.
                    let region = match parts.len() {
                        4 => Some(self.parse_desc(&parts[3], scope)?),
                        _ => None,
                    };
                    bindings.push(DoBinding { name, init: value, step, region });
                }
                let test_clause = self.list(&a[1]).ok_or_else(|| self.bad(s, "do test"))?.to_vec();
                if test_clause.is_empty() {
                    return Err(self.bad(s, "do test"));
                }
                let test = self.parse_exp(&test_clause[0], scope)?;
                let result = self.parse_body(&test_clause[1..], scope)?;
                let body = match a.len() {
                    2 => None,
                    _ => Some(self.parse_body(&a[2..], scope)?),
                };
                return Ok(self.arena.exp(span, Exp::Do { bindings, test, result, body }));
            }
        }

        let fun = self.parse_exp(&items[0], scope)?;
        let args = self.parse_exp_seq(a, scope)?;
        Ok(self.arena.exp(span, Exp::App { fun, args }))
    }

    fn parse_exp_seq(&mut self, items: &[Syntax], scope: &DScope) -> R<Vec<ExpId>> {
        let mut out = Vec::with_capacity(items.len());
        for item in items {
            out.push(self.parse_exp(item, scope)?);
        }
        Ok(out)
    }

    /// A body of one or more expressions, wrapped in `begin` if more than one.
    fn parse_body(&mut self, items: &[Syntax], scope: &DScope) -> R<ExpId> {
        let span = items.first().map_or(Span::new(fixpt_read::FileId(0), 0, 0), |s| s.span);
        let mut exps = self.parse_exp_seq(items, scope)?;
        if exps.len() == 1 {
            return Ok(exps.pop().expect("length checked"));
        }
        Ok(self.arena.exp(span, Exp::Begin(exps)))
    }

    /// `(lambda ((x type) …) …)`, where a parameter may name its region as a
    /// third element — `(x int @!)` — which makes the binding mutable.
    fn parse_params(&mut self, s: &Syntax, scope: &DScope) -> R<Vec<Param>> {
        let items = self.list(s).ok_or_else(|| self.bad(s, "parameter list"))?.to_vec();
        let mut out = Vec::with_capacity(items.len());
        for item in &items {
            let parts = self.list(item).ok_or_else(|| self.bad(item, "parameter"))?.to_vec();
            if parts.len() < 2 {
                return Err(self.bad(item, "parameter"));
            }
            let name = self.sym_of(&parts[0]).ok_or_else(|| self.bad(item, "parameter name"))?;
            let ty = self.parse_desc(&parts[1], scope)?;
            // A third element names the region the binding lives in. It does
            // *not* change the parameter's type.
            let region = match parts.len() {
                3 => Some(self.parse_desc(&parts[2], scope)?),
                _ => None,
            };
            out.push(Param { name, ty, region });
        }
        Ok(out)
    }

    // ---------------------------------------------------------- the sugar
    fn expand_let(
        &mut self,
        s: &Syntax,
        sequential: bool,
        a: &[Syntax],
        scope: &DScope,
    ) -> R<ExpId> {
        if a.is_empty() {
            return Err(self.bad(s, "let"));
        }
        let pairs = self.list(&a[0]).ok_or_else(|| self.bad(s, "let bindings"))?.to_vec();
        if sequential && pairs.len() > 1 {
            // `(let* ((a x) (b y)) body)` ⇒ `(let ((a x)) (let ((b y)) body))`
            let inner = {
                let mut rest = vec![a[0].clone()];
                rest[0] = Syntax {
                    span: a[0].span,
                    datum: Datum::List { items: pairs[1..].to_vec(), tail: None },
                };
                let mut form = vec![Syntax {
                    span: s.span,
                    datum: Datum::Symbol(self.syms.let_star),
                }];
                form.extend(rest);
                form.extend_from_slice(&a[1..]);
                Syntax { span: s.span, datum: Datum::List { items: form, tail: None } }
            };
            let outer_bindings =
                Syntax { span: a[0].span, datum: Datum::List { items: vec![pairs[0].clone()], tail: None } };
            return self.expand_let(s, false, &[outer_bindings, inner], scope);
        }

        // `let` cannot be `((lambda ((x <type>) …) body) e …)`, because a
        // `lambda` parameter needs a written type and `let` has none to give.
        // So it stays its own form: check the initialisers outside the scope,
        // bind, then check the body. That is also why it is not `letrec` — the
        // initialisers must not see the bindings.
        let mut bindings = Vec::with_capacity(pairs.len());
        for p in &pairs {
            let parts = self.list(p).ok_or_else(|| self.bad(p, "let binding"))?.to_vec();
            if parts.len() < 2 {
                return Err(self.bad(p, "let binding"));
            }
            let name = self.sym_of(&parts[0]).ok_or_else(|| self.bad(p, "let name"))?;
            let value = self.parse_exp(&parts[1], scope)?;
            // `(x 3 @!)` — a mutable binding. As with a parameter, the region
            // belongs to the binding rather than to the value's type.
            let region = match parts.len() {
                3 => Some(self.parse_desc(&parts[2], scope)?),
                _ => None,
            };
            bindings.push(Binding { name, value, region });
        }
        let body = self.parse_body(&a[1..], scope)?;
        Ok(self.arena.exp(s.span, Exp::Let { bindings, body }))
    }

    fn expand_and(&mut self, span: Span, a: &[Syntax], scope: &DScope) -> R<ExpId> {
        if a.is_empty() {
            return Ok(self.arena.exp(span, Exp::Bool(true)));
        }
        let first = self.parse_exp(&a[0], scope)?;
        if a.len() == 1 {
            return Ok(first);
        }
        let rest = self.expand_and(span, &a[1..], scope)?;
        let els = self.arena.exp(span, Exp::Bool(false));
        Ok(self.arena.exp(span, Exp::If { test: first, then: rest, els }))
    }

    fn expand_or(&mut self, span: Span, a: &[Syntax], scope: &DScope) -> R<ExpId> {
        if a.is_empty() {
            return Ok(self.arena.exp(span, Exp::Bool(false)));
        }
        let first = self.parse_exp(&a[0], scope)?;
        if a.len() == 1 {
            return Ok(first);
        }
        let rest = self.expand_or(span, &a[1..], scope)?;
        let then = self.arena.exp(span, Exp::Bool(true));
        Ok(self.arena.exp(span, Exp::If { test: first, then, els: rest }))
    }

    fn expand_cond(&mut self, span: Span, a: &[Syntax], scope: &DScope) -> R<ExpId> {
        if a.is_empty() {
            return Ok(self.arena.exp(span, Exp::Unit));
        }
        let clause = self.list(&a[0]).ok_or_else(|| self.bad(&a[0], "cond clause"))?.to_vec();
        if clause.is_empty() {
            return Err(self.bad(&a[0], "cond clause"));
        }
        if self.sym_of(&clause[0]) == Some(self.syms.else_) {
            return self.parse_body(&clause[1..], scope);
        }
        let test = self.parse_exp(&clause[0], scope)?;
        let then = self.parse_body(&clause[1..], scope)?;
        let els = self.expand_cond(span, &a[1..], scope)?;
        Ok(self.arena.exp(span, Exp::If { test, then, els }))
    }
}

impl Default for Parser {
    fn default() -> Parser {
        Parser::new()
    }
}
