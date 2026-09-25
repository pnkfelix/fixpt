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
    Define { name: Sym, ty: TyId, effect: Effect },
    /// `(define-type name …)`.
    DefineType { name: Sym, ty: TyId },
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
                Ok(Top::Exp(Checked { ty, effect }))
            }
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
                let r = self.parse_exp(init).and_then(|e| {
                    let (it, effect) = self.synth(e)?;
                    if !self.subtype(it, ty) {
                        return Err(FxError::at(
                            init.span,
                            format!(
                                "`{}` is declared a {}, and its definition is a {}",
                                self.interner.name(name),
                                self.show_ty(ty),
                                self.show_ty(it)
                            ),
                        ));
                    }
                    Ok(effect)
                });
                match r {
                    Ok(effect) => Ok(Top::Define { name, ty, effect }),
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
                Ok(Top::Define { name, ty, effect })
            }
            _ => Err(FxError::at(span, "`(define name type expression)` or `(define name expression)`")),
        }
    }

    /// Check `form` as [`top`](Self::top) would, then forget it: nothing it
    /// defines stays in scope and nothing it allocated stays in the arena.
    /// What checking-as-you-type needs, since a form half typed is not a form
    /// submitted. The caller restores the interner, which it owns.
    pub fn try_top<T>(&mut self, form: &Syntax, then: impl FnOnce(&mut Checker, R<Top>) -> T) -> T {
        let (env, dscope, arena) = (self.env.len(), self.dscope.len(), self.arena.mark());
        let r = self.top(form);
        let out = then(self, r);
        self.env.truncate(env);
        self.dscope.truncate(dscope);
        self.arena.reset(arena);
        out
    }

    /// Check a whole program written as text, keeping its definitions, and
    /// return what its last expression checked to.
    pub fn check_program(&mut self, text: &str) -> R<Checked> {
        let forms = self.read_in(FileId(0), text)?;
        let mut last = None;
        for f in &forms {
            if let Top::Exp(c) = self.top(f)? {
                last = Some(c);
            }
        }
        last.ok_or_else(|| FxError::at(Span::new(FileId(0), 0, 0), "the program has no expression"))
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

    /// What argument `index` (from 0) of the operator written `op` must be,
    /// when the operator checks and is a subroutine.
    pub fn argument_type(&mut self, op: &Syntax, index: usize) -> Option<TyId> {
        let mark = self.arena.mark();
        let found = self.parse_exp(op).ok().and_then(|e| self.synth(e).ok()).and_then(|(t, _)| {
            match self.arena.get(t) {
                crate::ast::Ty::Subr { params, .. } => params.get(index).copied(),
                _ => None,
            }
        });
        // The answer is a type that already existed or a parameter of one
        // just made; keep the arena only in the second case.
        match found {
            Some(t) => Some(t),
            None => {
                self.arena.reset(mark);
                None
            }
        }
    }
}

/// The words FX-26 reserves: syntax, and the parts of descriptions.
pub const KEYWORDS: &[&str] = &[
    "lambda", "plambda", "proj", "if", "letrec", "let", "begin", "define", "define-type",
    "subr", "poly", "ref", "pairof", "dletrec", "void", "pure", "maxeff", "read", "write",
    "alloc", "goto", "comefrom", "region", "effect", "type", "prompt", "prompt-tag",
    "composable", "mark-key", "listof",
];
