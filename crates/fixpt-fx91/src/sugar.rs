//! Desugaring — `sugar.scm`.
//!
//! Like the Scheme expander, and like the original, these rewrite to simpler
//! *syntax* and re-enter the parser rather than building abstract syntax
//! directly. `parse-cond` in `sugar.scm` is literally
//! `((parse-exp alpha-env) `(if ,test ,body (cond ,@rest)))`, and keeping that
//! shape is what makes each rule checkable against the report by eye.
//!
//! Two of these have surprises worth stating, because both look like bugs and
//! are not:
//!
//! * FX-91's `or` yields `#t`, not the value of the first true operand:
//!   `(or a b)` is `(if a #t (or b))`. In a typed language the disjuncts are
//!   already booleans, so there is nothing else it could return.
//! * `do` binds exactly **one** variable: its header is `(var init step)`, a
//!   single triple, not a list of them. `tests.fx` uses it that way throughout.

use crate::ast::{AlphaId, Fx, FxId, Kind};
use crate::error::{FxError, R};
use crate::parse::Parser;
use fixpt_read::{Datum, Span, Sym, Syntax};

/// `(head rest…)`
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

impl Parser<'_> {
    /// `sugar?`: the symbol `pure`, any symbol containing a dot, or a list
    /// headed by one of the seven sugar forms.
    pub(crate) fn is_sugar(&self, s: &Syntax) -> bool {
        match &s.datum {
            Datum::Symbol(x) => {
                *x == self.syms.pure || self.interner.name(*x).contains('.')
            }
            Datum::List { items, .. } => items
                .first()
                .and_then(|h| h.as_symbol())
                .is_some_and(|h| self.is_sugar_head(h)),
            _ => false,
        }
    }

    fn is_sugar_head(&self, h: Sym) -> bool {
        let sy = &self.syms;
        h == sy.and
            || h == sy.cond
            || h == sy.do_
            || h == sy.let_star
            || h == sy.letrec
            || h == sy.or
            || h == sy.match_
    }

    pub(crate) fn parse_sugar_dexp(&mut self, alpha: AlphaId, s: &Syntax) -> R<FxId> {
        match &s.datum {
            Datum::Symbol(_) => self.parse_sugar_symbol(alpha, s, true),
            _ => {
                let expanded = self.expand_sugar_form(s)?;
                self.parse_dexp(alpha, &expanded)
            }
        }
    }

    pub(crate) fn parse_sugar_exp(&mut self, alpha: AlphaId, s: &Syntax) -> R<FxId> {
        match &s.datum {
            Datum::Symbol(_) => self.parse_sugar_symbol(alpha, s, false),
            _ => {
                let expanded = self.expand_sugar_form(s)?;
                self.parse_exp(alpha, &expanded)
            }
        }
    }

    /// `pure`, and dot notation.
    ///
    /// The split is at the *first* dot only, and the remainder is re-parsed —
    /// which is what makes `a.b.c` mean `(with a (with b c))`, per report
    /// §2.4.7, rather than a field literally named `b.c`. A doubled dot,
    /// `m..x`, selects a description instead of a value.
    fn parse_sugar_symbol(&mut self, alpha: AlphaId, s: &Syntax, want_desc: bool) -> R<FxId> {
        let name_sym = s.as_symbol().expect("called on a symbol");
        if name_sym == self.syms.pure {
            let empty = form(s.span, self.syms.maxeff, vec![]);
            return self.parse_dexp(alpha, &empty);
        }
        let text = self.interner.name(name_sym).to_string();
        let Some(dot) = text.find('.') else {
            return Err(FxError::fatal(s.span, "unknown sugar symbol"));
        };
        let before = &text[..dot];
        let after = &text[dot + 1..];
        if let Some(rest) = after.strip_prefix('.') {
            // `m..x` is description selection.
            let m = self.interner.intern(before);
            let f = self.interner.intern(rest);
            let sel = form(s.span, self.syms.select, vec![sym(s.span, m), sym(s.span, f)]);
            return self.parse_dexp(alpha, &sel);
        }
        let m = self.interner.intern(before);
        let rest = self.interner.intern(after);
        let w = form(s.span, self.syms.with, vec![sym(s.span, m), sym(s.span, rest)]);
        // Re-entering parse_exp is what handles the remaining dots, if any.
        if want_desc { self.parse_dexp(alpha, &w) } else { self.parse_exp(alpha, &w) }
    }

    fn expand_sugar_form(&mut self, s: &Syntax) -> R<Syntax> {
        let items = s
            .as_proper_list()
            .ok_or_else(|| FxError::user(s.span, "a sugar form must be a list"))?;
        let head = items[0].as_symbol().expect("checked by is_sugar");
        let sy = self.syms.clone();
        if head == sy.cond {
            return self.expand_cond(s, items);
        }
        if head == sy.or {
            return self.expand_or_and(s, items, true);
        }
        if head == sy.and {
            return self.expand_or_and(s, items, false);
        }
        if head == sy.let_star {
            return self.expand_let_star(s, items);
        }
        if head == sy.letrec {
            return self.expand_letrec(s, items);
        }
        if head == sy.do_ {
            return self.expand_do(s, items);
        }
        if head == sy.match_ {
            return self.expand_match(s, items);
        }
        Err(FxError::fatal(s.span, "unknown sugar expression"))
    }

    /// `(cond (test result) …)`. Note that only the *second* element of a
    /// clause is its result — `parse-cond` takes `(cadadr exp)` — so a clause
    /// with extra forms silently drops them. Faithful.
    fn expand_cond(&mut self, s: &Syntax, items: &[Syntax]) -> R<Syntax> {
        if items.len() < 2 {
            return Err(FxError::user(s.span, "cond needs at least one clause"));
        }
        let clause = items[1]
            .as_proper_list()
            .ok_or_else(|| FxError::user(items[1].span, "a cond clause must be a list"))?;
        if clause.len() < 2 {
            return Err(FxError::user(items[1].span, "a cond clause is `(test result)`"));
        }
        if clause[0].as_symbol() == Some(self.syms.else_) {
            return Ok(clause[1].clone());
        }
        let mut rest = vec![sym(s.span, self.syms.cond)];
        rest.extend_from_slice(&items[2..]);
        Ok(form(
            s.span,
            self.syms.if_,
            vec![clause[0].clone(), clause[1].clone(), Syntax::list(s.span, rest)],
        ))
    }

    fn expand_or_and(&mut self, s: &Syntax, items: &[Syntax], is_or: bool) -> R<Syntax> {
        if items.len() == 1 {
            return Ok(Syntax::new(s.span, Datum::Bool(!is_or)));
        }
        let head = if is_or { self.syms.or } else { self.syms.and };
        let mut rest = vec![sym(s.span, head)];
        rest.extend_from_slice(&items[2..]);
        let rest = Syntax::list(s.span, rest);
        let (then, els) = if is_or {
            (Syntax::new(s.span, Datum::Bool(true)), rest)
        } else {
            (rest, Syntax::new(s.span, Datum::Bool(false)))
        };
        Ok(form(s.span, self.syms.if_, vec![items[1].clone(), then, els]))
    }

    fn expand_let_star(&mut self, s: &Syntax, items: &[Syntax]) -> R<Syntax> {
        if items.len() != 3 {
            return Err(FxError::user(s.span, "let* is `(let* bindings body)`"));
        }
        let bindings = items[1]
            .as_proper_list()
            .ok_or_else(|| FxError::user(items[1].span, "let* needs a binding list"))?;
        if bindings.is_empty() {
            return Ok(items[2].clone());
        }
        let inner = form(
            s.span,
            self.syms.let_star,
            vec![list(s.span, bindings[1..].to_vec()), items[2].clone()],
        );
        Ok(form(
            s.span,
            self.syms.let_,
            vec![list(s.span, vec![bindings[0].clone()]), inner],
        ))
    }

    /// `letrec` is a module and a `with` — which is how FX-91 gets mutual
    /// recursion without a dedicated form, since a module's definitions are
    /// already mutually visible.
    fn expand_letrec(&mut self, s: &Syntax, items: &[Syntax]) -> R<Syntax> {
        if items.len() != 3 {
            return Err(FxError::user(s.span, "letrec is `(letrec bindings body)`"));
        }
        let bindings = items[1]
            .as_proper_list()
            .ok_or_else(|| FxError::user(items[1].span, "letrec needs a binding list"))?;
        let name = self.new_identifier("letrec");
        let mut defs = vec![sym(s.span, self.syms.module)];
        for b in bindings {
            let parts = b
                .as_proper_list()
                .ok_or_else(|| FxError::user(b.span, "a letrec binding is `(name value)`"))?;
            if parts.len() != 2 {
                return Err(FxError::user(b.span, "a letrec binding is `(name value)`"));
            }
            defs.push(form(
                b.span,
                self.syms.define,
                vec![parts[0].clone(), parts[1].clone()],
            ));
        }
        let module = Syntax::list(s.span, defs);
        let binding = list(s.span, vec![sym(s.span, name), module]);
        let with = form(s.span, self.syms.with, vec![sym(s.span, name), items[2].clone()]);
        Ok(form(s.span, self.syms.let_, vec![list(s.span, vec![binding]), with]))
    }

    /// `(do (var init step) (test result) body)` — one variable, not a list.
    fn expand_do(&mut self, s: &Syntax, items: &[Syntax]) -> R<Syntax> {
        if items.len() != 4 {
            return Err(FxError::user(
                s.span,
                "do is `(do (var init step) (test result) body)`",
            ));
        }
        let header = items[1]
            .as_proper_list()
            .ok_or_else(|| FxError::user(items[1].span, "do's header is `(var init step)`"))?;
        if header.len() != 3 {
            return Err(FxError::user(items[1].span, "do's header is `(var init step)`"));
        }
        let test = items[2]
            .as_proper_list()
            .ok_or_else(|| FxError::user(items[2].span, "do's test is `(test result)`"))?;
        if test.len() != 2 {
            return Err(FxError::user(items[2].span, "do's test is `(test result)`"));
        }
        let name = self.new_identifier("do");
        let recur = Syntax::list(s.span, vec![sym(s.span, name), header[2].clone()]);
        let body = form(s.span, self.syms.begin, vec![items[3].clone(), recur]);
        let if_form =
            form(s.span, self.syms.if_, vec![test[0].clone(), test[1].clone(), body]);
        let lam = form(
            s.span,
            self.syms.lambda,
            vec![list(s.span, vec![header[0].clone()]), if_form],
        );
        let binding = list(s.span, vec![sym(s.span, name), lam]);
        let call = Syntax::list(s.span, vec![sym(s.span, name), header[1].clone()]);
        Ok(form(s.span, self.syms.letrec, vec![list(s.span, vec![binding]), call]))
    }

    // ------------------------------------------------------------- define
    /// `(define (f (x t)) e)` and `(define [f (t type)] e)` reduce to a plain
    /// `(define name value)`. The bracket form reaches here as
    /// `(define (proj f (t type)) e)`, courtesy of the reader's projection
    /// sugar.
    pub(crate) fn expand_define_sugar(&mut self, clause: &Syntax) -> R<Syntax> {
        let parts = clause
            .as_proper_list()
            .ok_or_else(|| FxError::user(clause.span, "a define clause must be a list"))?;
        if parts.len() != 3 {
            return Err(FxError::user(clause.span, "define is `(define name value)`"));
        }
        match &parts[1].datum {
            Datum::Symbol(_) => Ok(clause.clone()),
            Datum::List { items: head, .. } if !head.is_empty() => {
                let span = clause.span;
                if head[0].as_symbol() == Some(self.syms.proj) {
                    if head.len() < 2 {
                        return Err(FxError::user(span, "`[name binding…]` needs a name"));
                    }
                    let plam = form(
                        span,
                        self.syms.plambda,
                        vec![list(span, head[2..].to_vec()), parts[2].clone()],
                    );
                    let rebuilt =
                        form(span, self.syms.define, vec![head[1].clone(), plam]);
                    return self.expand_define_sugar(&rebuilt);
                }
                let lam = form(
                    span,
                    self.syms.lambda,
                    vec![list(span, head[1..].to_vec()), parts[2].clone()],
                );
                let rebuilt = form(span, self.syms.define, vec![head[0].clone(), lam]);
                self.expand_define_sugar(&rebuilt)
            }
            _ => Err(FxError::user(parts[1].span, "define needs a name")),
        }
    }

    /// `define-datatype` becomes an abstraction, a description of its
    /// representation, and a constructor/destructor pair per variant. Returns
    /// `None` for any other clause.
    pub(crate) fn expand_define_datatype(&mut self, clause: &Syntax) -> R<Option<Vec<Syntax>>> {
        let Some(parts) = clause.as_proper_list() else { return Ok(None) };
        if parts.first().and_then(|h| h.as_symbol()) != Some(self.syms.define_datatype) {
            return Ok(None);
        }
        if parts.len() < 2 {
            return Err(FxError::user(clause.span, "define-datatype needs a name"));
        }
        let span = clause.span;
        let sy = self.syms.clone();

        // `name` or `(name (arg kind)…)`
        let (name, args): (Syntax, Vec<Syntax>) = match &parts[1].datum {
            Datum::Symbol(_) => (parts[1].clone(), Vec::new()),
            Datum::List { items, .. } if !items.is_empty() => {
                (items[0].clone(), items[1..].to_vec())
            }
            _ => return Err(FxError::user(parts[1].span, "define-datatype needs a name")),
        };
        let name_sym = self.symbol_pub(&name)?;
        let applied = |me: &Self, n: Syntax| -> Syntax {
            let _ = me;
            if args.is_empty() {
                n
            } else {
                let mut xs = vec![n];
                for a in &args {
                    xs.push(a.as_proper_list().map(|p| p[0].clone()).unwrap_or_else(|| a.clone()));
                }
                Syntax::list(span, xs)
            }
        };

        let variants = &parts[2..];
        // `(productof (1 t1) (2 t2) …)` — labels are the 1-based position.
        let make_productof = |me: &mut Self, members: &[Syntax]| -> Syntax {
            let mut xs = vec![sym(span, sy.productof)];
            for (i, m) in members.iter().enumerate() {
                let label = me.interner.intern(&(i + 1).to_string());
                xs.push(list(span, vec![sym(span, label), m.clone()]));
            }
            Syntax::list(span, xs)
        };
        let mut sumof_items = vec![sym(span, sy.sumof)];
        for v in variants {
            let vp = v
                .as_proper_list()
                .ok_or_else(|| FxError::user(v.span, "a variant is `(tag type…)`"))?;
            if vp.is_empty() {
                return Err(FxError::user(v.span, "a variant needs a tag"));
            }
            let prod = make_productof(self, &vp[1..]);
            sumof_items.push(list(span, vec![vp[0].clone(), prod]));
        }
        let sumof = Syntax::list(span, sumof_items);

        let wrap = |body: Syntax| -> Syntax {
            if args.is_empty() {
                body
            } else {
                form(span, sy.dlambda, vec![list(span, args.clone()), body])
            }
        };
        let kind = if args.is_empty() {
            sym(span, sy.type_)
        } else {
            let mut xs = vec![sym(span, sy.dfunc)];
            for a in &args {
                xs.push(a.as_proper_list().map(|p| p[1].clone()).unwrap_or_else(|| a.clone()));
            }
            Syntax::list(span, xs)
        };

        let rep_name = {
            let text = format!("{}-rep", self.interner.name(name_sym));
            self.interner.intern(&text)
        };
        let mut out = vec![
            form(
                span,
                sy.define_abstraction,
                vec![name.clone(), kind, wrap(sumof.clone())],
            ),
            form(
                span,
                sy.define_description,
                vec![sym(span, rep_name), wrap(sumof)],
            ),
        ];

        let up = self.glue_pub(sy.up_prefix, name_sym);
        let down = self.glue_pub(sy.down_prefix, name_sym);
        let applied_name = applied(self, name.clone());
        let applied_rep = applied(self, sym(span, rep_name));

        for v in variants {
            let vp = v.as_proper_list().expect("checked above");
            let tag = vp[0].clone();
            let members = &vp[1..];
            let tag_sym = self.symbol_pub(&tag)?;
            let ids: Vec<Syntax> = members
                .iter()
                .map(|_| {
                    let base = self.interner.name(tag_sym).to_string();
                    let n = self.new_identifier(&base);
                    sym(span, n)
                })
                .collect();
            let bindings: Vec<Syntax> = ids
                .iter()
                .zip(members)
                .map(|(i, m)| list(span, vec![i.clone(), m.clone()]))
                .collect();

            // Constructor: (define-typed tag type (lambda … (up-name (sum …))))
            let ctor_type = form(
                span,
                sy.subr,
                vec![sym(span, sy.pure), list(span, bindings.clone()), applied_name.clone()],
            );
            let prod = make_productof(self, members);
            let mut sum_args = vec![sym(span, sy.sum), applied_rep.clone(), tag.clone()];
            let mut product_items = vec![sym(span, sy.product), prod.clone()];
            product_items.extend(ids.iter().cloned());
            sum_args.push(Syntax::list(span, product_items));
            let sum_expr = Syntax::list(span, sum_args);
            let ctor_body = form(
                span,
                sy.lambda,
                vec![
                    list(span, bindings.clone()),
                    Syntax::list(span, vec![sym(span, up), sum_expr]),
                ],
            );
            out.push(form(
                span,
                sy.define_typed,
                vec![
                    tag.clone(),
                    if args.is_empty() {
                        ctor_type.clone()
                    } else {
                        form(span, sy.poly, vec![list(span, args.clone()), ctor_type.clone()])
                    },
                    if args.is_empty() {
                        ctor_body.clone()
                    } else {
                        form(span, sy.plambda, vec![list(span, args.clone()), ctor_body.clone()])
                    },
                ],
            ));

            // Destructor: CPS, named `tag~`.
            let e_success = sym(span, self.new_identifier("e"));
            let e_failure = sym(span, self.new_identifier("e"));
            let t_result = sym(span, self.new_identifier("t"));
            let val = sym(span, self.new_identifier("val"));
            let untagged = sym(span, self.new_identifier("untagged"));
            let success = sym(span, self.new_identifier("s"));
            let failure = sym(span, self.new_identifier("f"));

            let splits: Vec<Syntax> = (0..members.len())
                .map(|i| {
                    let label = self.interner.intern(&(i + 1).to_string());
                    form(
                        span,
                        sy.extract,
                        vec![prod.clone(), untagged.clone(), sym(span, label)],
                    )
                })
                .collect();
            let succ_type = form(
                span,
                sy.subr,
                vec![e_success.clone(), list(span, bindings.clone()), t_result.clone()],
            );
            let fail_type = form(
                span,
                sy.subr,
                vec![
                    e_failure.clone(),
                    list(span, vec![list(span, vec![val.clone(), applied_name.clone()])]),
                    t_result.clone(),
                ],
            );
            let params = list(
                span,
                vec![
                    list(span, vec![val.clone(), applied_name.clone()]),
                    list(span, vec![success.clone(), succ_type.clone()]),
                    list(span, vec![failure.clone(), fail_type.clone()]),
                ],
            );
            let effect = form(span, sy.maxeff, vec![e_success.clone(), e_failure.clone()]);
            let dtor_type =
                form(span, sy.subr, vec![effect, params.clone(), t_result.clone()]);

            let mut succ_call = vec![success.clone()];
            succ_call.extend(splits);
            let on_success = form(
                span,
                sy.lambda,
                vec![list(span, vec![untagged.clone()]), Syntax::list(span, succ_call)],
            );
            let on_failure = form(
                span,
                sy.lambda,
                vec![
                    list(span, vec![untagged.clone()]),
                    Syntax::list(span, vec![failure.clone(), val.clone()]),
                ],
            );
            let tagcase = form(
                span,
                sy.tagcase,
                vec![
                    applied_rep.clone(),
                    Syntax::list(span, vec![sym(span, down), val.clone()]),
                    tag.clone(),
                    on_success,
                    on_failure,
                ],
            );
            let dtor_body = form(span, sy.lambda, vec![params, tagcase]);

            let mut poly_args = args.clone();
            poly_args.push(list(span, vec![e_success.clone(), sym(span, sy.effect)]));
            poly_args.push(list(span, vec![e_failure.clone(), sym(span, sy.effect)]));
            poly_args.push(list(span, vec![t_result.clone(), sym(span, sy.type_)]));

            let dtor_name = {
                let text = format!("{}~", self.interner.name(tag_sym));
                self.interner.intern(&text)
            };
            out.push(form(
                span,
                sy.define_typed,
                vec![
                    sym(span, dtor_name),
                    form(span, sy.poly, vec![list(span, poly_args.clone()), dtor_type]),
                    form(span, sy.plambda, vec![list(span, poly_args), dtor_body]),
                ],
            ));
        }
        Ok(Some(out))
    }
}

/// Free helper so `expand_define_datatype`'s closures can reach it.
impl Parser<'_> {
    pub(crate) fn symbol_pub(&self, s: &Syntax) -> R<Sym> {
        s.as_symbol().ok_or_else(|| FxError::user(s.span, "expected a symbol"))
    }
    pub(crate) fn glue_pub(&mut self, prefix: Sym, rest: Sym) -> Sym {
        let text = format!("{}{}", self.interner.name(prefix), self.interner.name(rest));
        self.interner.intern(&text)
    }
}

/// Kinds are compared structurally; this is `kind=?`.
pub fn kind_eq(a: &Kind, b: &Kind) -> bool {
    a == b
}

/// `unparse-exp`'s head symbol, for the trace output. Not needed for
/// conformance, but useful in errors.
pub fn head_name(fx: &Fx) -> &'static str {
    match fx {
        Fx::Forward(_) => "forward",
        Fx::Variable(_) => "variable",
        Fx::Unparsed { .. } => "unparsed",
        Fx::DLambda { .. } => "dlambda",
        Fx::DApp { .. } => "dapplication",
        Fx::Select { .. } => "select",
        Fx::MaxEff(_) => "maxeff",
        Fx::Subr { .. } => "subr",
        Fx::Poly { .. } => "poly",
        Fx::PolyTilde { .. } => "poly~",
        Fx::ModuleOf { .. } => "moduleof",
        Fx::SumOf { .. } => "sumof",
        Fx::ProductOf { .. } => "productof",
        Fx::Lambda { .. } => "lambda",
        Fx::Let { .. } => "let",
        Fx::App { .. } => "application",
        Fx::PLambda { .. } => "plambda",
        Fx::Proj { .. } => "proj",
        Fx::Module { .. } => "module",
        Fx::With { .. } => "with",
        Fx::Extend { .. } => "extend",
        Fx::If { .. } => "if",
        Fx::Open(_) => "open",
        Fx::Close(_) => "close",
        Fx::Begin(_) => "begin",
        Fx::Load { .. } => "load",
        Fx::The { .. } => "the",
        Fx::Does { .. } => "does",
        Fx::Sum { .. } => "sum",
        Fx::Product { .. } => "product",
        Fx::TagCase { .. } => "tagcase",
        Fx::Extract { .. } => "extract",
    }
}
