//! Programs: the top level, above the kernel.
//!
//! The kernel is expressions. A program is a sequence of top-level forms, each
//! of which may add to the environment the rest of the program sees:
//!
//! * `(define name type expression)` — `name` is a `type`. When the
//!   expression is a lambda, `name` is in scope in it, so the procedure may
//!   call itself (a one-binding `define-rec`); otherwise it is not.
//! * `(define name expression)` — the type is the expression's own; not
//!   recursive (a top-level `let`).
//! * `(define-rec (name type lambda) …)` — procedures that may call each
//!   other, each name in scope in every lambda (a top-level `letrec`). They
//!   are lambdas, so nothing runs before every one of them exists.
//! * `(define-type name type)` — a type abbreviation, which may mention itself
//!   (a top-level one-binding `dletrec`). Without it, a recursive type such as
//!   a continuation that is its own argument has to be written out in full at
//!   every use.
//! * `(define-effect name effect)` — an effect abbreviation, for the effect
//!   a group of procedures share.
//! * `(private-regions @r …)` — from here on, each `@r` is a fresh region no
//!   other program can name: the program is instantiated at regions of its
//!   own, as a `plambda` over them would be. What it does to them is masked
//!   from everything outside it, by construction (`crate::licence`).
//! * anything else is an expression, checked in the environment so far.

use crate::ast::{Effect, TyId};
use crate::check::{Checked, Checker};
use crate::error::{FxError, R};
use fixpt_read::{FileId, Reader, Span, Sym, Syntax, SyntaxProfile};

/// What one top-level form did.
#[derive(Clone, Debug)]
pub enum Top {
    /// `(define name …)`: `name` is bound to a value of this type, and
    /// computing it has this effect.
    /// `typed` when the type was written; `recursive` when the name is in
    /// scope in its expression, which is then a lambda.
    Define { name: Sym, ty: TyId, effect: Effect, exp: crate::ast::ExpId, typed: bool, recursive: bool },
    /// `(define-rec (name type lambda) …)`: each name bound to its lambda.
    DefineRec { bindings: Vec<(Sym, TyId, crate::ast::ExpId)> },
    /// `(define-type name …)`.
    DefineType { name: Sym, ty: TyId },
    /// `(define-type (name (param kind) …) …)`: a parametric abbreviation.
    DefineTypeFamily { name: Sym },
    /// `(define-effect name …)`: an abbreviation for an effect.
    DefineEffect { name: Sym, effect: Effect },
    /// `(private-regions @r …)`: the regions these names now stand for.
    PrivateRegions { regions: Vec<crate::ast::Region> },
    /// An expression.
    Exp(Checked),
}

impl Checker {
    /// Read `text` in FX-26's lexical syntax (`SyntaxProfile::FX26`),
    /// recording spans against `file`.
    pub fn read_in(&mut self, file: FileId, text: &str) -> R<Vec<Syntax>> {
        let mut interner = std::mem::take(&mut self.interner);
        let r = Reader::new(text, file, SyntaxProfile::FX26, &mut interner).read_all();
        self.interner = interner;
        let forms = r.map_err(|e| FxError::at(e.span, e.message))?;
        self.expand_forms(forms)
    }

    /// What is expanded as it is read (`define-datatype`), for forms read
    /// some other way: by the reader written in FX-26 (`crate::syn`).
    pub fn expand_forms(&mut self, forms: Vec<Syntax>) -> R<Vec<Syntax>> {
        let mut out = Vec::new();
        for f in forms {
            self.expand_datatype(f, &mut out)?;
        }
        Ok(out)
    }

    /// FX-91's `(define-datatype name (tag type …) …)`: a sum of products,
    /// each variant's members labelled from 1, and a constructor per tag,
    /// `(tag e …)`. Taken apart with `tagcase`, whose arm `(tag (x …) body)`
    /// names the members. Expanded as it is read, into the forms it stands
    /// for, so every way of running a program sees them.
    ///
    /// `(define-datatype (name (param kind) …) …)` has parameters: a type
    /// family, which its variants may mention with the same parameters, and
    /// constructors polymorphic in them.
    fn expand_datatype(&mut self, form: Syntax, out: &mut Vec<Syntax>) -> R<()> {
        let items = form.as_proper_list().unwrap_or(&[]).to_vec();
        if items.first().and_then(|h| h.as_symbol()).map(|h| self.interner.name(h)) != Some("define-datatype") {
            out.push(form);
            return Ok(());
        }
        let span = form.span;
        let [_, name, variants @ ..] = &items[..] else {
            return Err(FxError::at(span, "`(define-datatype name (tag type …) …)`"));
        };
        // The name, and the parameters, if it has any: `(name (param kind) …)`.
        let (name, family) = match name.as_proper_list() {
            Some([n, ps @ ..]) if n.as_symbol().is_some() => (n.clone(), Some(ps.to_vec())),
            _ => (name.clone(), None),
        };
        let name = &name;
        if name.as_symbol().is_none() || variants.is_empty() {
            return Err(FxError::at(span, "`(define-datatype name (tag type …) …)`"));
        }
        // What the type is called where it is used: `name`, or `(name param …)`.
        let mut used = name.clone();
        if let Some(ps) = &family {
            let mut u = vec![name.clone()];
            for p in ps {
                match p.as_proper_list() {
                    Some([n, _]) if n.as_symbol().is_some() => u.push(n.clone()),
                    _ => return Err(FxError::at(p.span, "a parameter is `(name kind)`")),
                }
            }
            used = Syntax::list(span, u);
        }
        let mut sym = |s: &str| Syntax::symbol(span, self.interner.intern(s));
        let (define_type, define, sumof, productof, subr, pure, lambda, sum, product, poly) = (
            sym("define-type"),
            sym("define"),
            sym("sumof"),
            sym("productof"),
            sym("subr"),
            sym("pure"),
            sym("lambda"),
            sym("sum"),
            sym("product"),
            sym("poly"),
        );
        let int = |n: usize| Syntax::new(span, fixpt_read::Datum::Number(fixpt_read::Num::Int(n as i64)));
        let list = |items: Vec<Syntax>| {
            if items.is_empty() { Syntax::new(span, fixpt_read::Datum::Nil) } else { Syntax::list(span, items) }
        };
        let mut arms = vec![sumof];
        let mut ctors = Vec::new();
        for v in variants {
            let parts = v.as_proper_list().unwrap_or(&[]).to_vec();
            let Some((tag, members)) = parts.split_first().filter(|(t, _)| t.as_symbol().is_some()) else {
                return Err(FxError::at(v.span, "a variant is `(tag type …)`"));
            };
            let mut prod = vec![productof.clone()];
            let mut params = Vec::new();
            let mut fields = vec![product.clone()];
            for (i, m) in members.iter().enumerate() {
                prod.push(list(vec![int(i + 1), m.clone()]));
                let x = Syntax::symbol(span, self.interner.intern(&format!("%x{}", i + 1)));
                params.push(x.clone());
                fields.push(list(vec![int(i + 1), x]));
            }
            arms.push(list(vec![tag.clone(), list(prod)]));
            let mut ty = list(vec![subr.clone(), pure.clone(), list(members.to_vec()), used.clone()]);
            if let Some(ps) = &family {
                ty = list(vec![poly.clone(), list(ps.clone()), ty]);
            }
            let body = list(vec![sum.clone(), tag.clone(), list(fields)]);
            ctors.push(list(vec![define.clone(), tag.clone(), ty, list(vec![lambda.clone(), list(params), body])]));
        }
        let head = match &family {
            Some(ps) => {
                let mut h = vec![name.clone()];
                h.extend(ps.iter().cloned());
                list(h)
            }
            None => name.clone(),
        };
        out.push(list(vec![define_type, head, list(arms)]));
        out.extend(ctors);
        Ok(())
    }

    /// Check one top-level form, keeping what it defines.
    pub fn top(&mut self, form: &Syntax) -> R<Top> {
        let items = form.as_proper_list().unwrap_or(&[]);
        let head = items.first().and_then(|h| h.as_symbol()).map(|h| self.interner.name(h));
        match head {
            Some("define") => self.define(form.span, items),
            Some("define-rec") => self.define_rec(form.span, items),
            Some("private-regions") => {
                let mut regions = Vec::new();
                for r in &items[1..] {
                    let name = self.binder_name(r)?;
                    if !self.interner.name(name).starts_with('@') {
                        return Err(FxError::at(r.span, "a region constant is written `@name`"));
                    }
                    let base = self.interner.name(name).to_string();
                    let fresh = self.fresh_region_named(&base);
                    self.dscope.push((name, crate::parse::DScope::Private(fresh)));
                    self.private_regions.push(fresh);
                    regions.push(fresh);
                }
                Ok(Top::PrivateRegions { regions })
            }
            Some("define-effect") => {
                let [_, name, def] = items else {
                    return Err(FxError::at(form.span, "`(define-effect name effect)`"));
                };
                let name = self.binder_name(name)?;
                let effect = self.parse_effect(def)?;
                self.dscope.push((name, crate::parse::DScope::Eff(effect.clone())));
                Ok(Top::DefineEffect { name, effect })
            }
            Some("define-type") => {
                let [_, name, def] = items else {
                    return Err(FxError::at(form.span, "`(define-type name type)`"));
                };
                if let Some([n, params @ ..]) = name.as_proper_list() {
                    let n = self.binder_name(n)?;
                    let params = Syntax::list(name.span, params.to_vec());
                    self.define_type_family(n, &params, def)?;
                    return Ok(Top::DefineTypeFamily { name: n });
                }
                let name = self.binder_name(name)?;
                let ty = self.define_type(name, def, form.span)?;
                Ok(Top::DefineType { name, ty })
            }
            _ => {
                let e = self.parse_exp(form)?;
                let (ty, effect) = self.synth(e)?;
                Ok(Top::Exp(Checked { ty, effect, exp: e }))
            }
        }
    }

    /// Put the binders of every `poly` at the top of `t` in scope for parsing.
    fn bind_signature(&mut self, t: TyId) {
        let mut t = self.arena.resolve(t);
        while let crate::ast::Ty::Poly { binders, body } = self.arena.get(t).clone() {
            for (v, k) in binders {
                let name = self.arena.dvar_name(v);
                self.dscope.push((name, crate::parse::DScope::Var(v, k)));
            }
            t = self.arena.resolve(body);
        }
    }

    fn binder_name(&self, s: &Syntax) -> R<Sym> {
        s.as_symbol().ok_or_else(|| FxError::at(s.span, "expected a name"))
    }

    fn define(&mut self, span: Span, items: &[Syntax]) -> R<Top> {
        match items {
            [_, name, ty, init] => {
                let name = self.binder_name(name)?;
                let ty = self.parse_type(ty)?;
                // A signature's binders are in scope in the definition, which
                // is checked against it: `(define id (poly ((t type)) …)
                // (lambda ((x t)) x))` means what a `plambda` would.
                let depth = self.dscope.len();
                self.bind_signature(ty);
                let e = self.parse_exp(init);
                self.dscope.truncate(depth);
                let e = e?;
                // A lambda is in scope in itself, as a `letrec` binding is:
                // making it runs nothing, so nothing sees it unmade.
                let recursive = self.is_lambda(e);
                if recursive {
                    self.env.push((name, ty));
                    self.known.insert((name, ty));
                }
                // A lambda whose every run ends needs no `spin`.
                let spins = recursive && !self.terminates(&[(name, ty, e)]);
                if spins {
                    self.recursive.push((name, ty));
                }
                let checked = self.check_declared(name, ty, e);
                if spins {
                    self.recursive.pop();
                }
                match checked {
                    Ok(effect) => {
                        if !recursive {
                            self.env.push((name, ty));
                        }
                        Ok(Top::Define { name, ty, effect, exp: e, typed: true, recursive })
                    }
                    Err(err) => {
                        if recursive {
                            self.env.pop();
                        }
                        Err(err)
                    }
                }
            }
            [_, name, init] => {
                let name = self.binder_name(name)?;
                let e = self.parse_exp(init)?;
                let (ty, effect) = self.synth(e)?;
                if self.is_lambda(e) {
                    self.known.insert((name, ty));
                }
                self.env.push((name, ty));
                Ok(Top::Define { name, ty, effect, exp: e, typed: false, recursive: false })
            }
            _ => Err(FxError::at(span, "`(define name type expression)` or `(define name expression)`")),
        }
    }

    /// `(define-rec (name type lambda) …)`: every name in scope first, then
    /// each lambda checked against its type.
    fn define_rec(&mut self, span: Span, items: &[Syntax]) -> R<Top> {
        let depth = self.env.len();
        let rdepth = self.recursive.len();
        let r = (|| {
            let mut parts = Vec::new();
            for b in &items[1..] {
                let Some([name, ty, init]) = b.as_proper_list() else {
                    return Err(FxError::at(b.span, "a define-rec binding is `(name type lambda)`"));
                };
                let name = self.binder_name(name)?;
                let ty = self.parse_type(ty)?;
                self.env.push((name, ty));
                self.known.insert((name, ty));
                parts.push((name, ty, init.clone()));
            }
            if parts.is_empty() {
                return Err(FxError::at(span, "`(define-rec (name type lambda) …)`"));
            }
            let mut bindings = Vec::new();
            for (name, ty, init) in parts {
                let d = self.dscope.len();
                self.bind_signature(ty);
                let e = self.parse_exp(&init);
                self.dscope.truncate(d);
                let e = e?;
                if !self.is_lambda(e) {
                    return Err(FxError::at(self.arena.span_of(e), crate::check::letrec_not_lambda(self.interner.name(name))));
                }
                bindings.push((name, ty, e));
            }
            // A group whose every run ends needs no `spin`.
            if !self.terminates(&bindings) {
                self.recursive.extend(bindings.iter().map(|(n, t, _)| (*n, *t)));
            }
            for (name, ty, e) in &bindings {
                self.check_declared(*name, *ty, *e)?;
            }
            Ok(Top::DefineRec { bindings })
        })();
        self.recursive.truncate(rdepth);
        if r.is_err() {
            self.env.truncate(depth);
        }
        r
    }

    /// Check `e` against `ty`, the type `name` is declared; an error at `e`
    /// itself says so.
    fn check_declared(&mut self, name: Sym, ty: TyId, e: crate::ast::ExpId) -> R<Effect> {
        self.check(e, ty).map_err(|err| {
            if err.span == self.arena.span_of(e) {
                FxError::at(err.span, format!("`{}` is declared a {}: {}", self.interner.name(name), self.show_ty(ty), err.message))
            } else {
                err
            }
        })
    }

    /// Check `form` as [`top`](Self::top) would, then forget it: nothing it
    /// defines stays in scope and nothing it allocated stays in the arena.
    /// What checking-as-you-type needs, since a form half typed is not a form
    /// submitted. The caller restores the interner, which it owns.
    pub fn try_top<T>(&mut self, form: &Syntax, then: impl FnOnce(&mut Checker, R<Top>) -> T) -> T {
        self.scratch(|c| {
            let r = c.top(form);
            then(c, r)
        })
    }

    /// Check a whole program written as text, keeping its definitions, and
    /// return what its last expression checked to.
    pub fn check_program(&mut self, text: &str) -> R<Checked> {
        let forms = self.read_in(FileId(0), text)?;
        let done = self.declare_ahead(&forms)?;
        let mut last = None;
        for (f, done) in forms.iter().zip(done) {
            if done {
                continue;
            }
            if let Top::Exp(c) = self.top(f)? {
                last = Some(c);
            }
        }
        last.ok_or_else(|| FxError::at(Span::new(FileId(0), 0, 0), "the program has no expression"))
    }

    /// The first of a whole program's two passes: every `define-type` and
    /// `define-effect` is processed, so that types can refer to each other in
    /// any order. Values cannot: a definition sees only those before it, and
    /// procedures that call each other are a `define-rec`. Returns, for each
    /// form, whether it is finished with (the abbreviations are). The second
    /// pass is `top` on the rest, in order.
    pub fn declare_ahead(&mut self, forms: &[Syntax]) -> R<Vec<bool>> {
        let mut done = Vec::new();
        for f in forms {
            let items = f.as_proper_list().unwrap_or(&[]);
            let head = items.first().and_then(|h| h.as_symbol()).map(|h| self.interner.name(h).to_string());
            match (head.as_deref(), items) {
                (Some("define-type" | "define-effect" | "private-regions"), _) => {
                    self.top(f)?;
                    done.push(true);
                }
                _ => done.push(false),
            }
        }
        Ok(done)
    }

    /// The names a program may use: every value and every type abbreviation
    /// in scope, innermost last, with shadowed ones left out.
    pub fn value_names(&self) -> Vec<Sym> {
        let mut out: Vec<Sym> = Vec::new();
        for (n, _) in self.env.iter().rev() {
            if !out.contains(n) {
                out.push(*n);
            }
        }
        out
    }

    /// The type a name is bound to, if it is a value.
    pub fn type_of_name(&self, name: Sym) -> Option<TyId> {
        self.env.iter().rev().find(|(n, _)| *n == name).map(|(_, t)| *t)
    }

    /// The type a name abbreviates, if `define-type` bound it.
    pub fn type_named(&self, name: Sym) -> Option<TyId> {
        self.dscope.iter().rev().find_map(|(n, d)| match d {
            crate::parse::DScope::Rec(t) if *n == name => Some(*t),
            _ => None,
        })
    }

    /// Every type abbreviation in scope.
    pub fn type_names(&self) -> Vec<Sym> {
        self.dscope
            .iter()
            .filter(|(_, d)| matches!(d, crate::parse::DScope::Rec(_)))
            .map(|(n, _)| *n)
            .collect()
    }

    /// The base types' names.
    pub fn base_names(&self) -> Vec<Sym> {
        self.base.keys().copied().collect()
    }

    /// Run `f`, then forget everything it added to the environment, the
    /// description scope and the arena. The caller restores the interner.
    pub fn scratch<T>(&mut self, f: impl FnOnce(&mut Checker) -> T) -> T {
        let (env, dscope, arena) = (self.env.len(), self.dscope.len(), self.arena.mark());
        let private = self.private_regions.len();
        let out = f(self);
        self.env.truncate(env);
        self.dscope.truncate(dscope);
        self.private_regions.truncate(private);
        self.facts.forget_from(arena.exps());
        self.arena.reset(arena);
        out
    }

    /// What the argument at `index` (from 1) of the application written
    /// `items` must be, given the operator and the other arguments — as
    /// text, since the type is forgotten with the rest of the scratch work.
    /// A binder nothing has fixed yet shows as its own name.
    pub fn describe_argument(&mut self, items: &[Syntax], index: usize) -> Option<String> {
        self.scratch(|c| {
            let op = c.parse_exp(items.first()?).ok()?;
            let others: Vec<(usize, crate::ast::ExpId)> = items
                .iter()
                .enumerate()
                .skip(1)
                .filter(|(i, _)| *i != index)
                .filter_map(|(i, s)| Some((i - 1, c.parse_exp(s).ok()?)))
                .collect();
            let t = c.argument_want(op, &others, index - 1)?;
            Some(c.show_ty(t))
        })
    }
}

/// The words FX-26 reserves: syntax, and the parts of descriptions.
pub const KEYWORDS: &[&str] = &[
    "lambda", "plambda", "proj", "if", "letrec", "let", "begin", "define", "define-type",
    "subr", "poly", "ref", "pairof", "dletrec", "void", "pure", "maxeff", "read", "write",
    "alloc", "goto", "comefrom", "region", "effect", "type", "prompt", "prompt-tag",
    "composable", "mark-key", "listof", "cond", "else", "and", "or", "let*", "define-effect", "private-regions", "the",
    "bloblet", "fields", "frozen", "arrayof", "icell", "await", "define-rec", "letrena", "letreap", "rlambda", "quote", "productof", "sumof", "product", "extract", "sum", "tagcase",
    "define-datatype", "make-bloblet", "bloblet-ref", "bloblet-set!", "bloblet-freeze", "bloblet-byte",
    "bloblet-set-byte!", "bloblet-bytes", "rmake-bloblet",
];
