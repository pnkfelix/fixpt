//! `match` and its quasiquote patterns — the rest of `sugar.scm`.
//!
//! A pattern is compiled into nested CPS calls to *destructors*. `(kons x rest)`
//! as a pattern does not call the constructor `kons`; it calls a procedure of
//! that name taking the value, a success continuation and a failure
//! continuation. That is why `define-datatype` generates a `tag~` destructor
//! alongside every `tag` constructor, and why the archive's own documentation
//! insists patterns use the distinct deconstructor name.
//!
//! Both folds here run **right to left**, because `utils.scm`'s `reduce` is a
//! right fold: each clause wraps the expansion of the clauses after it as its
//! own failure continuation, so the first clause ends up outermost and is
//! therefore tried first. Folding the other way would silently reverse clause
//! order.

use crate::error::{FxError, R};
use crate::parse::Parser;
use fixpt_read::{Datum, Span, Sym, Syntax};

fn form(span: Span, head: Sym, mut rest: Vec<Syntax>) -> Syntax {
    let mut items = vec![Syntax::symbol(span, head)];
    items.append(&mut rest);
    Syntax::list(span, items)
}
fn sym(span: Span, s: Sym) -> Syntax {
    Syntax::symbol(span, s)
}
fn list(span: Span, items: Vec<Syntax>) -> Syntax {
    if items.is_empty() { Syntax::new(span, Datum::Nil) } else { Syntax::list(span, items) }
}

/// Which mode a quasiquote subterm came back in.
#[derive(Copy, Clone, PartialEq, Eq)]
enum Mode {
    Quote,
    Unquote,
    UnquoteSplicing,
}

impl Parser {
    pub(crate) fn expand_match(&mut self, s: &Syntax, items: &[Syntax]) -> R<Syntax> {
        if items.len() < 2 {
            return Err(FxError::user(s.span, "match needs a subject"));
        }
        let span = s.span;
        let init = self.new_identifier("match");
        let fail = self.new_identifier("fail");
        let identity = self.new_identifier("identity");
        let sy = self.syms.clone();

        let x = self.interner.intern("x");
        let fail_lambda = form(
            span,
            sy.lambda,
            vec![
                list(span, vec![sym(span, x)]),
                Syntax::list(span, vec![sym(span, sy.unspecified)]),
            ],
        );
        let identity_lambda =
            form(span, sy.lambda, vec![list(span, vec![sym(span, x)]), sym(span, x)]);

        let body = self.match_clauses(span, &items[2..], init, identity, fail)?;
        let bindings = list(
            span,
            vec![
                list(span, vec![sym(span, init), items[1].clone()]),
                list(span, vec![sym(span, fail), fail_lambda]),
                list(span, vec![sym(span, identity), identity_lambda]),
            ],
        );
        Ok(form(span, sy.let_, vec![bindings, body]))
    }

    fn match_clauses(
        &mut self,
        span: Span,
        clauses: &[Syntax],
        val: Sym,
        succ: Sym,
        fail: Sym,
    ) -> R<Syntax> {
        let mut expansion =
            Syntax::list(span, vec![sym(span, fail), sym(span, val)]);
        // Right fold: the last clause is innermost.
        for clause in clauses.iter().rev() {
            let parts = clause
                .as_proper_list()
                .ok_or_else(|| FxError::user(clause.span, "a match clause is `(pattern body)`"))?;
            if parts.len() != 2 {
                return Err(FxError::user(clause.span, "a match clause is `(pattern body)`"));
            }
            let success =
                Syntax::list(span, vec![sym(span, succ), parts[1].clone()]);
            expansion =
                self.match_pattern(&parts[0], sym(span, val), success, expansion)?;
        }
        Ok(expansion)
    }

    fn match_pattern(
        &mut self,
        pattern: &Syntax,
        val: Syntax,
        success: Syntax,
        failure: Syntax,
    ) -> R<Syntax> {
        let span = pattern.span;
        let sy = self.syms.clone();

        if let Some(eq) = self.literal_equality(pattern) {
            let test = Syntax::list(span, vec![eq, pattern.clone(), val]);
            return Ok(form(span, sy.if_, vec![test, success, failure]));
        }
        if let Some(name) = pattern.as_symbol() {
            // `_` matches anything and binds nothing.
            if name == sy.underscore {
                return Ok(success);
            }
            let binding = list(span, vec![pattern.clone(), val]);
            return Ok(form(span, sy.let_, vec![list(span, vec![binding]), success]));
        }
        let parts = pattern
            .as_proper_list()
            .ok_or_else(|| FxError::user(span, "a pattern must be a symbol, literal or list"))?;
        if parts.is_empty() {
            return Err(FxError::user(span, "an empty pattern"));
        }
        if parts[0].as_symbol() == Some(sy.quasiquote) {
            if parts.len() != 2 {
                return Err(FxError::user(span, "quasiquote takes one subform"));
            }
            let rewritten = self.expand_quasiquote_pattern(&parts[1], 0)?;
            return self.match_pattern(&rewritten, val, success, failure);
        }

        // A constructor pattern: call the destructor with the value and two
        // continuations.
        let fail_fun = self.new_identifier("fail");
        let ids: Vec<Sym> =
            parts[1..].iter().map(|_| self.new_identifier("pattern")).collect();
        let mut inner = success;
        // Right fold again, so the first sub-pattern is outermost.
        for (sub, id) in parts[1..].iter().zip(&ids).rev() {
            let on_fail = Syntax::list(span, vec![sym(span, fail_fun)]);
            inner = self.match_pattern(sub, sym(span, *id), inner, on_fail)?;
        }
        let ok = form(
            span,
            sy.lambda,
            vec![list(span, ids.iter().map(|i| sym(span, *i)).collect()), inner],
        );
        let x = self.interner.intern("x");
        let no = form(
            span,
            sy.lambda,
            vec![
                list(span, vec![sym(span, x)]),
                Syntax::list(span, vec![sym(span, fail_fun)]),
            ],
        );
        let call = Syntax::list(span, vec![parts[0].clone(), val, ok, no]);
        let thunk = form(
            span,
            sy.lambda,
            vec![Syntax::new(span, Datum::Nil), failure],
        );
        let binding = list(span, vec![sym(span, fail_fun), thunk]);
        Ok(form(span, sy.let_, vec![list(span, vec![binding]), call]))
    }

    /// The equality procedure for a literal pattern, as source.
    ///
    /// These are spliced as code, exactly as `standard.scm` stores them —
    /// including `unit`'s, which it registers as the *quoted* datum
    /// `'(lambda (x y) #t)` rather than an unquoted one. Splicing that yields
    /// `((quote (lambda (x y) #t)) p v)`, an application of a quoted list. It
    /// is a real latent bug in the original and is reproduced rather than
    /// quietly repaired, so the corpus keeps telling the truth about it.
    fn literal_equality(&mut self, pattern: &Syntax) -> Option<Syntax> {
        let span = pattern.span;
        let sy = self.syms.clone();
        let named = |me: &mut Self, name: &str| Some(sym(span, me.interner.intern(name)));
        match &pattern.datum {
            Datum::Bool(_) => named(self, "equiv?"),
            Datum::Symbol(x) if *x == sy.unit_value => {
                let x1 = self.interner.intern("x");
                let y1 = self.interner.intern("y");
                let lam = form(
                    span,
                    sy.lambda,
                    vec![
                        list(span, vec![sym(span, x1), sym(span, y1)]),
                        Syntax::new(span, Datum::Bool(true)),
                    ],
                );
                Some(form(span, sy.quote, vec![lam]))
            }
            Datum::Number(n) if crate::parse::is_scheme_integer_pub(n) => named(self, "="),
            Datum::Number(_) => named(self, "fl="),
            Datum::Char(_) => named(self, "char=?"),
            Datum::Str(_) => named(self, "string=?"),
            Datum::Symbol(x) if *x == sy.nil => {
                let x1 = self.interner.intern("x");
                let y1 = self.interner.intern("y");
                let null_q = self.interner.intern("null?");
                Some(form(
                    span,
                    sy.lambda,
                    vec![
                        list(span, vec![sym(span, x1), sym(span, y1)]),
                        Syntax::list(span, vec![sym(span, null_q), sym(span, y1)]),
                    ],
                ))
            }
            Datum::List { items, .. } => match items.first().and_then(|h| h.as_symbol()) {
                Some(h) if h == sy.symbol => named(self, "sym=?"),
                Some(h) if h == sy.quote => named(self, "sexp=?"),
                _ => None,
            },
            _ => None,
        }
    }

    /// Jonathan Rees's quasiquote expander, adapted for *patterns*: the output
    /// is a pattern built from `cons~`, `nil~` and the `…->sexp~` destructors,
    /// which `match_pattern` then compiles like any other constructor pattern.
    fn expand_quasiquote_pattern(&mut self, x: &Syntax, level: u32) -> R<Syntax> {
        let (mode, arg) = self.descend(x, level)?;
        self.finalize(mode, arg, x.span)
    }

    fn finalize(&mut self, mode: Mode, arg: Syntax, span: Span) -> R<Syntax> {
        match mode {
            Mode::Quote => Ok(form(span, self.syms.quote, vec![arg])),
            Mode::Unquote => Ok(arg),
            Mode::UnquoteSplicing => {
                Err(FxError::user(span, ",@ in an illegal context"))
            }
        }
    }

    fn descend(&mut self, x: &Syntax, level: u32) -> R<(Mode, Syntax)> {
        let sy = self.syms.clone();
        // `_` is a wildcard even inside a quasiquote.
        if x.as_symbol() == Some(sy.underscore) {
            return Ok((Mode::Unquote, x.clone()));
        }
        let Some(items) = x.as_proper_list() else {
            return Ok((Mode::Quote, x.clone()));
        };
        if items.len() == 2 {
            let head = items[0].as_symbol();
            if head == Some(sy.unquote) {
                if level == 0 {
                    return Ok((Mode::Unquote, items[1].clone()));
                }
                return self.descend_interesting(x, level - 1, sy.unquoted_to_sexp);
            }
            if head == Some(sy.unquote_splicing) {
                if level == 0 {
                    return Ok((Mode::UnquoteSplicing, items[1].clone()));
                }
                return self.descend_interesting(
                    x,
                    level - 1,
                    sy.unquoted_splicing_to_sexp,
                );
            }
            if head == Some(sy.quasiquote) {
                return self.descend_interesting(x, level + 1, sy.quasiquoted_to_sexp);
            }
            if head == Some(sy.quote) {
                return self.descend_interesting(x, level, sy.quoted_to_sexp);
            }
        }
        self.descend_list(x, items, level)
    }

    fn descend_interesting(&mut self, x: &Syntax, level: u32, inject: Sym) -> R<(Mode, Syntax)> {
        let items = x.as_proper_list().expect("checked by the caller");
        let (mode, arg) = self.descend(&items[1], level)?;
        if mode == Mode::Quote {
            return Ok((Mode::Quote, x.clone()));
        }
        let finalized = self.finalize(mode, arg, x.span)?;
        Ok((Mode::Unquote, form(x.span, inject, vec![finalized])))
    }

    fn descend_list(&mut self, x: &Syntax, items: &[Syntax], level: u32) -> R<(Mode, Syntax)> {
        let span = x.span;
        let sy = self.syms.clone();
        let (mode, arg) = self.descend_tail(span, items, level)?;
        if mode == Mode::Quote {
            return Ok((Mode::Quote, x.clone()));
        }
        Ok((Mode::Unquote, form(span, sy.list_to_sexp, vec![arg])))
    }

    /// Build the list pattern right to left, so a `,@` splice can only appear
    /// where the tail is already empty — the one case the original allows.
    fn descend_tail(&mut self, span: Span, items: &[Syntax], level: u32) -> R<(Mode, Syntax)> {
        let sy = self.syms.clone();
        if items.is_empty() {
            return Ok((Mode::Unquote, Syntax::list(span, vec![sym(span, sy.null_tilde)])));
        }
        let (cdr_mode, cdr_arg) = self.descend_tail(span, &items[1..], level)?;
        let (car_mode, car_arg) = self.descend(&items[0], level)?;
        if car_mode == Mode::Quote && cdr_mode == Mode::Quote {
            return Ok((Mode::Quote, Syntax::list(span, items.to_vec())));
        }
        if car_mode == Mode::UnquoteSplicing {
            let tail_is_empty = cdr_mode == Mode::Unquote
                && cdr_arg
                    .as_proper_list()
                    .is_some_and(|p| p.len() == 1 && p[0].as_symbol() == Some(sy.null_tilde));
            if tail_is_empty {
                return Ok((Mode::Unquote, car_arg));
            }
            return Err(FxError::user(span, "illegal use of @ in a quasiquoted pattern"));
        }
        let car = self.finalize(car_mode, car_arg, span)?;
        let cdr = self.finalize(cdr_mode, cdr_arg, span)?;
        Ok((Mode::Unquote, form(span, sy.cons_tilde, vec![car, cdr])))
    }
}
