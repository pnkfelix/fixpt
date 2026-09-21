//! Lowering checked FX-91 to Scheme — `code.scm`.
//!
//! Types and effects are *erased*: `plambda`, `proj`, `the`, `open` and
//! `close` all disappear, leaving their subject. What survives is the value
//! computation, expressed in three runtime shapes:
//!
//! ```text
//! (*module* ((name value) …))   a module
//! (*sum* tag value)             a sumof value
//! (*product* #(v …))            a productof value
//! ```
//!
//! Output is Scheme *syntax*, not Core IR directly, for the same reason the
//! original emits Scheme: `code-of-variable` emits a variable's **user** name,
//! so two distinct alpha-renamed variables can produce the same identifier.
//! That is only sound because the generated code's lexical structure mirrors
//! the FX expression's, and it takes a real Scheme expander to exploit it.
//! Going straight to Core IR would mean re-deriving the scoping that Scheme
//! already does correctly.

use crate::ast::{Fx, FxId, LiteralValue};
use crate::check::Checker;
use crate::error::{FxError, R};
use fixpt_read::{Datum, Span, Sym, Syntax};

impl Checker {
    fn s(&mut self, span: Span, name: &str) -> Syntax {
        let sym = self.p.interner.intern(name);
        Syntax::symbol(span, sym)
    }

    fn call(&mut self, span: Span, head: &str, mut args: Vec<Syntax>) -> Syntax {
        let mut items = vec![self.s(span, head)];
        items.append(&mut args);
        Syntax::list(span, items)
    }

    fn quoted(&mut self, span: Span, datum: Syntax) -> Syntax {
        self.call(span, "quote", vec![datum])
    }

    /// `rename-scheme-keyword`: FX's `set!` would otherwise collide with
    /// Scheme's special form.
    fn emit_name(&mut self, span: Span, user: Sym) -> Syntax {
        let text = self.p.interner.name(user).to_string();
        let renamed = if text == "set!" { "set!-1" } else { &text };
        self.s(span, renamed)
    }

    /// The entry point: checked FX-91 expression to Scheme syntax.
    pub fn code_of_exp(&mut self, id: FxId) -> R<Syntax> {
        let span = self.p.arena.span(id);
        // A literal carries its value, and that value *is* the code.
        if let Some(lit) = self.p.arena.exp_info(id).literal.clone() {
            return Ok(match lit {
                LiteralValue::SelfEvaluating(s) => s,
                LiteralValue::Sexp(datum) => {
                    let converted = self.quoted_to_sexp(&datum)?;
                    self.quoted(span, converted)
                }
            });
        }
        Ok(match self.p.arena.get(id).clone() {
            Fx::Variable(v) => self.emit_name(span, v.user_name),

            Fx::Lambda { ids, body, .. } => {
                let params: Vec<Syntax> = ids
                    .iter()
                    .map(|i| {
                        let u = self.p.arena.var(*i).expect("a variable").user_name;
                        self.emit_name(span, u)
                    })
                    .collect();
                let body = self.code_of_exp(body)?;
                self.call(span, "lambda", vec![Syntax::list(span, params), body])
            }

            Fx::Let { ids, exps, body } => {
                let mut bindings = Vec::with_capacity(ids.len());
                for (i, e) in ids.iter().zip(&exps) {
                    let u = self.p.arena.var(*i).expect("a variable").user_name;
                    let name = self.emit_name(span, u);
                    let value = self.code_of_exp(*e)?;
                    bindings.push(Syntax::list(span, vec![name, value]));
                }
                let body = self.code_of_exp(body)?;
                self.call(span, "let", vec![Syntax::list(span, bindings), body])
            }

            // Erased: the type abstraction has no run-time content.
            Fx::PLambda { body, .. } => self.code_of_exp(body)?,
            Fx::Proj { exp, .. }
            | Fx::The { exp, .. }
            | Fx::Does { exp, .. }
            | Fx::Open(exp)
            | Fx::Close(exp) => self.code_of_exp(exp)?,

            Fx::Module { .. } => self.code_of_module(id)?,
            Fx::With { .. } => self.code_of_with(id)?,
            Fx::Extend { .. } => self.code_of_extend(id)?,

            Fx::App { rator, rands } => {
                let mut items = vec![self.code_of_exp(rator)?];
                for r in &rands {
                    items.push(self.code_of_exp(*r)?);
                }
                Syntax::list(span, items)
            }

            Fx::If { test, then, els } => {
                let t = self.code_of_exp(test)?;
                let c = self.code_of_exp(then)?;
                let a = self.code_of_exp(els)?;
                self.call(span, "if", vec![t, c, a])
            }

            Fx::Begin(exps) => {
                let mut items = Vec::with_capacity(exps.len());
                for e in &exps {
                    items.push(self.code_of_exp(*e)?);
                }
                self.call(span, "begin", items)
            }

            Fx::Load { parsed: Some(node), .. } => self.code_of_exp(node)?,
            Fx::Load { path, .. } => {
                return Err(FxError::fatal(span, format!("{path} was never parsed")));
            }

            Fx::Sum { tag, exp, .. } => {
                let tag_sym = Syntax::symbol(span, tag);
                let quoted_tag = self.quoted(span, tag_sym);
                let star = self.s(span, "*sum*");
                let quoted_star = self.quoted(span, star);
                let value = self.code_of_exp(exp)?;
                self.call(span, "list", vec![quoted_star, quoted_tag, value])
            }

            Fx::Product { exps, .. } => {
                let mut items = Vec::with_capacity(exps.len());
                for e in &exps {
                    items.push(self.code_of_exp(*e)?);
                }
                let vector = self.call(span, "vector", items);
                let star = self.s(span, "*product*");
                let quoted_star = self.quoted(span, star);
                self.call(span, "list", vec![quoted_star, vector])
            }

            Fx::TagCase { exp, tag, success, failure, .. } => {
                let name = { let text = self.fresh("sum"); self.p.interner.intern(&text) };
                let var = Syntax::symbol(span, name);
                let subject = self.code_of_exp(exp)?;
                let binding =
                    Syntax::list(span, vec![Syntax::list(span, vec![var.clone(), subject])]);
                let tag_sym = Syntax::symbol(span, tag);
                let quoted_tag = self.quoted(span, tag_sym);
                let got = self.call(span, "cadr", vec![var.clone()]);
                let test = self.call(span, "eq?", vec![quoted_tag, got]);
                let payload = self.call(span, "caddr", vec![var.clone()]);
                let on_ok = self.code_of_exp(success)?;
                let ok = Syntax::list(span, vec![on_ok, payload]);
                let on_no = self.code_of_exp(failure)?;
                let no = Syntax::list(span, vec![on_no, var]);
                let branch = self.call(span, "if", vec![test, ok, no]);
                self.call(span, "let", vec![binding, branch])
            }

            Fx::Extract { ty, exp, tag } => {
                // The field's position comes from the *type*, so extraction is
                // a constant index rather than a search.
                let productof = self.value_of_dexp(ty)?;
                let Fx::ProductOf { tags, .. } = self.p.arena.get(productof).clone() else {
                    return Err(FxError::fatal(span, "extract on a non-productof"));
                };
                let Some(index) = tags.iter().position(|t| *t == tag) else {
                    return Err(FxError::fatal(span, "extract tag is not in the productof"));
                };
                let subject = self.code_of_exp(exp)?;
                let fields = self.call(span, "cadr", vec![subject]);
                let i = Syntax::new(span, Datum::Number(fixpt_read::Num::Int(index as i64)));
                self.call(span, "vector-ref", vec![fields, i])
            }

            other => {
                return Err(FxError::fatal(
                    span,
                    format!("unknown expression in code-of-exp: {}", crate::sugar::head_name(&other)),
                ));
            }
        })
    }

    fn fresh(&mut self, base: &str) -> String {
        self.p.arena.gensym_counter += 1;
        format!("{base}-{}", self.p.arena.gensym_counter)
    }

    /// A module becomes an association list, tagged so `with` can recognise it.
    /// The `up-`/`down-` coercions are the identity: abstraction is entirely a
    /// static notion, with no run-time representation at all.
    fn code_of_module(&mut self, id: FxId) -> R<Syntax> {
        let span = self.p.arena.span(id);
        let Fx::Module {
            up_ids,
            down_ids,
            define_ids,
            define_exps,
            typed_ids,
            typed_exps,
            ..
        } = self.p.arena.get(id).clone()
        else {
            unreachable!()
        };

        let mut coercions = Vec::new();
        for c in up_ids.iter().chain(&down_ids) {
            let u = self.p.arena.var(*c).expect("a variable").user_name;
            let name = self.emit_name(span, u);
            let x = self.s(span, "x");
            let identity =
                self.call(span, "lambda", vec![Syntax::list(span, vec![x.clone()]), x]);
            coercions.push(Syntax::list(span, vec![name, identity]));
        }

        let mut ids = define_ids.clone();
        ids.extend(typed_ids.iter().copied());
        let mut exps = define_exps.clone();
        exps.extend(typed_exps.iter().copied());

        let mut bindings = Vec::with_capacity(ids.len());
        let mut entries = Vec::with_capacity(ids.len());
        for (i, e) in ids.iter().zip(&exps) {
            let u = self.p.arena.var(*i).expect("a variable").user_name;
            let name = self.emit_name(span, u);
            let value = self.code_of_exp(*e)?;
            bindings.push(Syntax::list(span, vec![name.clone(), value]));
            let quoted = self.quoted(span, name.clone());
            entries.push(self.call(span, "list", vec![quoted, name]));
        }
        let alist = self.call(span, "list", entries);
        let star = self.s(span, "*module*");
        let quoted_star = self.quoted(span, star);
        let result = self.call(span, "list", vec![quoted_star, alist]);
        let body = self.call(span, "letrec", vec![Syntax::list(span, bindings), result]);
        if coercions.is_empty() {
            return Ok(body);
        }
        Ok(self.call(span, "let", vec![Syntax::list(span, coercions), body]))
    }

    /// `with` destructures the association list into ordinary bindings.
    ///
    /// The built-in `fx` module is the exception: its value is the marker
    /// `(*module* fx)` and its bindings are already global, so the body is used
    /// directly rather than being wrapped in a `let` over nothing.
    fn code_of_with(&mut self, id: FxId) -> R<Syntax> {
        let span = self.p.arena.span(id);
        let Fx::With { module, body, .. } = self.p.arena.get(id).clone() else { unreachable!() };
        let val_ids = self.module_val_ids(module)?;
        let mod_name = { let text = self.fresh("*module-list*"); self.p.interner.intern(&text) };
        let mod_var = Syntax::symbol(span, mod_name);

        let module_code = self.code_of_exp(module)?;
        let alist = self.call(span, "cadr", vec![module_code]);
        let outer =
            Syntax::list(span, vec![Syntax::list(span, vec![mod_var.clone(), alist])]);

        let fx = self.s(span, "fx");
        let quoted_fx = self.quoted(span, fx);
        let is_fx = self.call(span, "eq?", vec![mod_var.clone(), quoted_fx]);

        let body_code = self.code_of_exp(body)?;
        let mut bindings = Vec::with_capacity(val_ids.len());
        for i in &val_ids {
            let u = self.p.arena.var(*i).expect("a variable").user_name;
            let name = self.emit_name(span, u);
            let quoted = self.quoted(span, name.clone());
            let entry = self.call(span, "assq", vec![quoted, mod_var.clone()]);
            let value = self.call(span, "cadr", vec![entry]);
            bindings.push(Syntax::list(span, vec![name, value]));
        }
        let unpacked = if bindings.is_empty() {
            body_code.clone()
        } else {
            self.call(span, "let", vec![Syntax::list(span, bindings), body_code.clone()])
        };
        let branch = self.call(span, "if", vec![is_fx, body_code, unpacked]);
        Ok(self.call(span, "let", vec![outer, branch]))
    }

    /// `extend` takes the extension's bindings and appends whatever the base
    /// module exported that the extension did not shadow.
    fn code_of_extend(&mut self, id: FxId) -> R<Syntax> {
        let span = self.p.arena.span(id);
        let Fx::Extend { module, body, .. } = self.p.arena.get(id).clone() else {
            unreachable!()
        };
        let val_ids = self.module_val_ids(module)?;
        let mod1 = {
            let n = { let text = self.fresh("mod1"); self.p.interner.intern(&text) };
            Syntax::symbol(span, n)
        };
        let mod2 = {
            let n = { let text = self.fresh("mod2"); self.p.interner.intern(&text) };
            Syntax::symbol(span, n)
        };
        let pair1 = {
            let n = { let text = self.fresh("pair1"); self.p.interner.intern(&text) };
            Syntax::symbol(span, n)
        };
        let rest = {
            let n = { let text = self.fresh("rest"); self.p.interner.intern(&text) };
            Syntax::symbol(span, n)
        };

        let module_code = self.code_of_exp(module)?;
        let mut bindings = vec![Syntax::list(span, vec![mod1.clone(), module_code])];
        for i in &val_ids {
            let u = self.p.arena.var(*i).expect("a variable").user_name;
            let name = self.emit_name(span, u);
            let quoted = self.quoted(span, name.clone());
            let alist = self.call(span, "cadr", vec![mod1.clone()]);
            let entry = self.call(span, "assq", vec![quoted, alist]);
            let value = self.call(span, "cadr", vec![entry]);
            bindings.push(Syntax::list(span, vec![name, value]));
        }
        let body_code = self.code_of_exp(body)?;
        bindings.push(Syntax::list(span, vec![mod2.clone(), body_code]));

        // (do ((pair1 (cadr mod1) (cdr pair1))
        //      (rest '() (if (assv (caar pair1) (cadr mod2)) rest (cons pair1 rest))))
        //     ((null? pair1) rest))
        let alist1 = self.call(span, "cadr", vec![mod1.clone()]);
        let step1 = self.call(span, "cdr", vec![pair1.clone()]);
        let spec1 = Syntax::list(span, vec![pair1.clone(), alist1, step1]);
        let nil = Syntax::new(span, Datum::Nil);
        let empty = self.quoted(span, nil);
        let key = self.call(span, "caar", vec![pair1.clone()]);
        let alist2 = self.call(span, "cadr", vec![mod2.clone()]);
        let found = self.call(span, "assv", vec![key, alist2]);
        let consed = self.call(span, "cons", vec![pair1.clone(), rest.clone()]);
        let step2 = self.call(span, "if", vec![found, rest.clone(), consed]);
        let spec2 = Syntax::list(span, vec![rest.clone(), empty, step2]);
        let done = self.call(span, "null?", vec![pair1]);
        let test = Syntax::list(span, vec![done, rest]);
        let loop_form = self.call(
            span,
            "do",
            vec![Syntax::list(span, vec![spec1, spec2]), test],
        );

        let head = self.call(span, "cadr", vec![mod2]);
        let merged = self.call(span, "append", vec![head, loop_form]);
        let star = self.s(span, "*module*");
        let quoted_star = self.quoted(span, star);
        let result = self.call(span, "list", vec![quoted_star, merged]);
        Ok(self.call(span, "let*", vec![Syntax::list(span, bindings), result]))
    }

    fn module_val_ids(&mut self, module: FxId) -> R<Vec<FxId>> {
        let ty = self.type_of_exp(module)?;
        match self.p.arena.get(ty) {
            Fx::ModuleOf { val_ids, .. } => Ok(val_ids.clone()),
            _ => Err(FxError::fatal(self.p.arena.span(module), "expected a module type")),
        }
    }

    /// `quoted-to-sexp`: a quoted datum becomes `sexp`'s tagged representation,
    /// so that `'(1 2)` is a value of type `sexp` rather than a Scheme list.
    fn quoted_to_sexp(&mut self, datum: &Syntax) -> R<Syntax> {
        let span = datum.span;
        // This is quoted *data*, not code: the vector has to be an actual
        // vector datum. Emitting `(vector u)` here would leave a literal
        // three-element list where a vector was meant, and the failure surfaces
        // much later as "expected a vector".
        let wrap = |me: &mut Self, tag: &str, value: Syntax| -> Syntax {
            let tag = me.s(span, tag);
            let vector = Syntax::new(span, Datum::Vector(vec![value]));
            let star = me.s(span, "*product*");
            let product = Syntax::list(span, vec![star, vector]);
            let sum = me.s(span, "*sum*");
            Syntax::list(span, vec![sum, tag, product])
        };
        Ok(match &datum.datum {
            Datum::Bool(_) => wrap(self, "bool->sexp", datum.clone()),
            Datum::Number(n) => {
                let tag = if crate::parse::is_scheme_integer_pub(n) {
                    "int->sexp"
                } else {
                    "float->sexp"
                };
                wrap(self, tag, datum.clone())
            }
            Datum::Char(_) => wrap(self, "char->sexp", datum.clone()),
            Datum::Str(_) => wrap(self, "string->sexp", datum.clone()),
            Datum::Symbol(s) => {
                // `an-unit` inside a quotation stands for the unit value.
                if *s == self.p.syms.an_unit {
                    let u = Syntax::symbol(span, self.p.syms.unit_value);
                    wrap(self, "unit->sexp", u)
                } else {
                    wrap(self, "sym->sexp", datum.clone())
                }
            }
            Datum::Nil => {
                let empty = Syntax::new(span, Datum::Nil);
                wrap(self, "list->sexp", empty)
            }
            Datum::List { items, tail } => {
                let mut converted = Vec::with_capacity(items.len());
                for i in items {
                    converted.push(self.quoted_to_sexp(i)?);
                }
                let list = match tail {
                    None => Syntax::list(span, converted),
                    Some(t) => {
                        let t = self.quoted_to_sexp(t)?;
                        Syntax::new(
                            span,
                            Datum::List { items: converted, tail: Some(Box::new(t)) },
                        )
                    }
                };
                wrap(self, "list->sexp", list)
            }
            Datum::Vector(items) => {
                let mut converted = Vec::with_capacity(items.len());
                for i in items {
                    converted.push(self.quoted_to_sexp(i)?);
                }
                wrap(self, "vector->sexp", Syntax::new(span, Datum::Vector(converted)))
            }
            Datum::Bytevector(_) => {
                return Err(FxError::fatal(span, "a bytevector is not an FX-91 datum"));
            }
        })
    }
}
