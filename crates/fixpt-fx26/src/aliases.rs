//! A procedural macro's aliases, where they are checked (`macros::
//! procedural`; `TODO.md` §228): `%~N:x`, which an expansion bound, is a
//! name of its own; one it left free is the top level's `x`, `(with
//! #%toplevel x)`, what it means where the macro was defined, whatever binds
//! `x` where it is used. Decided here, with the binders of the expression
//! known, once it is read; a description's alias is decided as it is read
//! (`Checker::read_qualified`), and a keyword's and a label's are the
//! keyword and the label (`procedural::keywords`, `Checker::label`).

use crate::ast::{Exp, ExpId, ModItem};
use crate::check::Checker;
use crate::macros::procedural::alias_base;
use crate::R;
use fixpt_read::{Sym, Syntax};

impl Checker {
    /// `s` read as an expression, a top level's, its aliases decided
    /// (`resolve_aliases`), `defining` in scope: what the form defines.
    pub(crate) fn parse_top_exp(&mut self, s: &Syntax, defining: &[Sym]) -> R<ExpId> {
        let e = self.parse_exp(s)?;
        self.resolve_aliases(e, &mut defining.to_vec());
        Ok(e)
    }

    /// Each alias in `e` that nothing binds where it is, `bound` those that
    /// are around it, nor the top level defined (the expansion's own
    /// definitions): the top level's name.
    pub(crate) fn resolve_aliases(&mut self, e: ExpId, bound: &mut Vec<Sym>) {
        match self.arena.exp_at(e).clone() {
            Exp::Var(s) => {
                if bound.contains(&s) || self.lookup(s).is_some() {
                    return;
                }
                let Some(base) = alias_base(self.interner.name(s)).map(str::to_string) else { return };
                let span = self.arena.span_of(e);
                let n = self.interner.intern(&base);
                let body = self.arena.exp(span, Exp::Var(n));
                let module = self.interner.intern("#%toplevel");
                self.arena.replace_exp(e, Exp::With { module, body });
            }
            Exp::Int(_) | Exp::Bool(_) | Exp::Str(_) | Exp::Char(_) | Exp::Float(_) | Exp::Symbol(_) | Exp::Unit => {}
            Exp::Lambda { params, body } => {
                let depth = bound.len();
                bound.extend(params.iter().map(|(n, _)| *n));
                self.resolve_aliases(body, bound);
                bound.truncate(depth);
            }
            Exp::App { fun, args } => {
                self.resolve_aliases(fun, bound);
                for a in args {
                    self.resolve_aliases(a, bound);
                }
            }
            Exp::PLambda { body, .. } | Exp::Proj { body, .. } | Exp::LetRegion { body, .. } => self.resolve_aliases(body, bound),
            Exp::RLambda { region, lambda } => {
                self.resolve_aliases(region, bound);
                self.resolve_aliases(lambda, bound);
            }
            Exp::If { test, then, els } => {
                for x in [test, then, els] {
                    self.resolve_aliases(x, bound);
                }
            }
            Exp::Letrec { bindings, body } => {
                let depth = bound.len();
                bound.extend(bindings.iter().map(|(n, _, _)| *n));
                for (_, _, init) in &bindings {
                    self.resolve_aliases(*init, bound);
                }
                self.resolve_aliases(body, bound);
                bound.truncate(depth);
            }
            Exp::Let { bindings, body } => {
                for (_, init) in &bindings {
                    self.resolve_aliases(*init, bound);
                }
                let depth = bound.len();
                bound.extend(bindings.iter().map(|(n, _)| *n));
                self.resolve_aliases(body, bound);
                bound.truncate(depth);
            }
            Exp::Module(items) => {
                let depth = bound.len();
                for item in &items {
                    match item {
                        ModItem::Abs { up, down, .. } => bound.extend([*up, *down]),
                        ModItem::Desc { .. } => {}
                        ModItem::Val { name, .. } => bound.push(*name),
                        ModItem::Rec(group) => bound.extend(group.iter().map(|(n, _, _)| *n)),
                    }
                }
                for item in &items {
                    match item {
                        ModItem::Val { init, .. } => self.resolve_aliases(*init, bound),
                        ModItem::Rec(group) => {
                            for (_, _, init) in group {
                                self.resolve_aliases(*init, bound);
                            }
                        }
                        _ => {}
                    }
                }
                bound.truncate(depth);
            }
            // A module's names in its body are its own: an alias there is
            // not one of them, which no alias can be.
            Exp::With { module, body } => {
                if !self.is_fx_module(module) && !self.is_toplevel_module(module) {
                    self.resolve_aliases(body, bound);
                }
            }
            Exp::Begin(items) => {
                for i in items {
                    self.resolve_aliases(i, bound);
                }
            }
            Exp::Prompt { tag, body, handler } => {
                for x in [tag, body, handler] {
                    self.resolve_aliases(x, bound);
                }
            }
            Exp::The { exp, .. } | Exp::Convention { exp, .. } | Exp::Extract(exp, _) | Exp::Sum(_, exp) => self.resolve_aliases(exp, bound),
            Exp::Bloblet { args, .. } => {
                for a in args {
                    self.resolve_aliases(a, bound);
                }
            }
            Exp::Product(fields) => {
                for (_, x) in fields {
                    self.resolve_aliases(x, bound);
                }
            }
            Exp::TagCase { scrutinee, arms, els } => {
                self.resolve_aliases(scrutinee, bound);
                for arm in &arms {
                    let depth = bound.len();
                    bound.extend(arm.names());
                    self.resolve_aliases(arm.body, bound);
                    bound.truncate(depth);
                }
                if let Some((y, body)) = els {
                    bound.push(y);
                    self.resolve_aliases(body, bound);
                    bound.pop();
                }
            }
        }
    }
}
