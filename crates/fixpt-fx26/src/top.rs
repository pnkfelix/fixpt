//! Programs: the top level, above the kernel.
//!
//! The kernel is expressions. A program is a sequence of top-level forms, each
//! of which may add to the environment the rest of the program sees:
//!
//! * `(define name type expression)` — `name` is a `type`, and is in scope in
//!   its own `expression`, so a definition may be recursive (a top-level
//!   `letrec` binding).
//! * `(define name expression)` — the type is the expression's own; not
//!   recursive (a top-level `let`).
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
    Define { name: Sym, ty: TyId, effect: Effect, exp: crate::ast::ExpId, recursive: bool },
    /// `(define-type name …)`.
    DefineType { name: Sym, ty: TyId },
    /// `(define-effect name …)`: an abbreviation for an effect.
    DefineEffect { name: Sym, effect: Effect },
    /// `(private-regions @r …)`: the regions these names now stand for.
    PrivateRegions { regions: Vec<crate::ast::Region> },
    /// An expression.
    Exp(Checked),
}

impl Checker {
    /// Read `text` in FX-26's lexical syntax, which is FX-87's, recording
    /// spans against `file`.
    pub fn read_in(&mut self, file: FileId, text: &str) -> R<Vec<Syntax>> {
        let mut interner = std::mem::take(&mut self.interner);
        let r = Reader::new(text, file, SyntaxProfile::FX87, &mut interner).read_all();
        self.interner = interner;
        r.map_err(|e| FxError::at(e.span, e.message))
    }

    /// Check one top-level form, keeping what it defines.
    pub fn top(&mut self, form: &Syntax) -> R<Top> {
        let items = form.as_proper_list().unwrap_or(&[]);
        let head = items.first().and_then(|h| h.as_symbol()).map(|h| self.interner.name(h));
        match head {
            Some("define") => self.define(form.span, items),
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
                // In scope in its own initialiser, as a `letrec` binding is.
                self.env.push((name, ty));
                // A signature's binders are in scope in the definition, which
                // is checked against it: `(define id (poly ((t type)) …)
                // (lambda ((x t)) x))` means what a `plambda` would.
                let depth = self.dscope.len();
                self.bind_signature(ty);
                let r = self.parse_exp(init);
                self.dscope.truncate(depth);
                let r = r.and_then(|e| {
                    self.check(e, ty).map(|eff| (eff, e)).map_err(|err| {
                        if err.span == self.arena.span_of(e) {
                            FxError::at(
                                err.span,
                                format!("`{}` is declared a {}: {}", self.interner.name(name), self.show_ty(ty), err.message),
                            )
                        } else {
                            err
                        }
                    })
                });
                match r {
                    Ok((effect, exp)) => Ok(Top::Define { name, ty, effect, exp, recursive: true }),
                    Err(e) => {
                        self.env.pop();
                        Err(e)
                    }
                }
            }
            [_, name, init] => {
                let name = self.binder_name(name)?;
                let e = self.parse_exp(init)?;
                let (ty, effect) = self.synth(e)?;
                self.env.push((name, ty));
                Ok(Top::Define { name, ty, effect, exp: e, recursive: false })
            }
            _ => Err(FxError::at(span, "`(define name type expression)` or `(define name expression)`")),
        }
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
    /// `define-effect` is processed, and every `define` with a signature is
    /// declared, so that the definitions can refer to each other in any
    /// order — which is what a signature is for. Returns, for each form,
    /// whether it is finished with (the abbreviations are). The second pass
    /// is `top` on the rest, in order.
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
                (Some("define"), [_, name, ty, _]) => {
                    let name = self.binder_name(name)?;
                    let ty = self.parse_type(ty)?;
                    self.env.push((name, ty));
                    done.push(false);
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
];
