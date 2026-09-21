//! Turning abstract syntax back into readable form — `token.scm`'s
//! `unparse-dexp` and `unparse-exp`.
//!
//! This is not a debugging convenience: the conformance goldens *are* this
//! function's output, so it has to agree with the original down to the choice
//! of head symbol. Two places where the printed form differs from the form you
//! write:
//!
//! * `subr` prints as `->`. Both read; only one prints.
//! * A `poly~` type scheme prints as `(~ …)`, which is deliberately not
//!   readable syntax — schemes are internal, so seeing one in output means
//!   something leaked.
//!
//! An expression with a cached literal value prints as that value rather than
//! as itself, which is why `3` appears in a type context rather than `an-int`.

use crate::ast::{Arena, Fx, FxId, Kind, LiteralValue};
use fixpt_read::{Datum, Interner, Span, Syntax};

pub struct Unparser<'a> {
    pub arena: &'a Arena,
    pub interner: &'a Interner,
    /// `*display-full-variable-name*`. Off by default; on, every variable
    /// prints with its alpha number, which is invaluable when a type looks
    /// right but unifies wrong.
    pub full_names: bool,
    /// `*show-original-module-text*`, on by default: a module inside a type
    /// prints as the source the user wrote.
    pub original_module_text: bool,
}

impl<'a> Unparser<'a> {
    pub fn new(arena: &'a Arena, interner: &'a Interner) -> Unparser<'a> {
        Unparser { arena, interner, full_names: false, original_module_text: true }
    }

    fn span(&self, id: FxId) -> Span {
        self.arena.span(id)
    }

    fn sym(&self, span: Span, name: &str) -> Syntax {
        // The interner is shared and immutable here, so printed-only names are
        // built as raw data rather than interned.
        Syntax::new(span, Datum::Str(name.to_string()))
    }

    fn word(&self, span: Span, name: &str) -> Syntax {
        // Words are emitted through a private datum so that printing does not
        // require mutating the interner; `render` turns them back into bare
        // text.
        self.sym(span, name)
    }

    fn list(&self, span: Span, items: Vec<Syntax>) -> Syntax {
        if items.is_empty() { Syntax::new(span, Datum::Nil) } else { Syntax::list(span, items) }
    }

    pub fn kind(&self, span: Span, k: &Kind) -> Syntax {
        match k {
            Kind::Type => self.word(span, "type"),
            Kind::Effect => self.word(span, "effect"),
            Kind::DFunc(ks) => {
                let mut items = vec![self.word(span, "->>")];
                items.extend(ks.iter().map(|k| self.kind(span, k)));
                self.list(span, items)
            }
        }
    }

    pub fn dexp(&self, id: FxId) -> Syntax {
        let span = self.span(id);
        match self.arena.get(id) {
            Fx::Variable(_) => self.variable(id),
            Fx::Unparsed { syntax, .. } => syntax.clone(),
            Fx::DLambda { ids, kinds, body } => {
                let bindings = self.kind_bindings(span, ids, kinds);
                self.list(
                    span,
                    vec![self.word(span, "dlambda"), bindings, self.dexp(*body)],
                )
            }
            Fx::Select { module, id: field } => self.list(
                span,
                vec![
                    self.word(span, "select"),
                    self.exp(*module),
                    self.word(span, self.interner.name(*field)),
                ],
            ),
            Fx::MaxEff(effects) => {
                let mut items = vec![self.word(span, "maxeff")];
                items.extend(effects.iter().map(|e| self.dexp(*e)));
                self.list(span, items)
            }
            // `subr` prints as `->`.
            Fx::Subr { effect, ids, types, body } => {
                let bindings: Vec<Syntax> = ids
                    .iter()
                    .zip(types)
                    .map(|(i, t)| self.list(span, vec![self.dexp(*i), self.dexp(*t)]))
                    .collect();
                self.list(
                    span,
                    vec![
                        self.word(span, "->"),
                        self.dexp(*effect),
                        self.list(span, bindings),
                        self.dexp(*body),
                    ],
                )
            }
            Fx::Poly { ids, kinds, body } => {
                let bindings = self.kind_bindings(span, ids, kinds);
                self.list(span, vec![self.word(span, "poly"), bindings, self.dexp(*body)])
            }
            Fx::PolyTilde { ids, kinds, body, .. } => self.list(
                span,
                vec![
                    self.word(span, "~"),
                    self.list(span, ids.iter().map(|i| self.dexp(*i)).collect()),
                    self.list(span, kinds.iter().map(|k| self.kind(span, k)).collect()),
                    self.dexp(*body),
                ],
            ),
            Fx::ModuleOf { abs_ids, abs_kinds, desc_ids, desc_descs, val_ids, val_types } => {
                let mut items = vec![self.word(span, "moduleof")];
                for (i, k) in abs_ids.iter().zip(abs_kinds) {
                    items.push(self.list(
                        span,
                        vec![self.word(span, "abs"), self.dexp(*i), self.kind(span, k)],
                    ));
                }
                for (i, d) in desc_ids.iter().zip(desc_descs) {
                    items.push(self.list(
                        span,
                        vec![self.word(span, "desc"), self.dexp(*i), self.dexp(*d)],
                    ));
                }
                for (i, t) in val_ids.iter().zip(val_types) {
                    items.push(self.list(
                        span,
                        vec![self.word(span, "val"), self.dexp(*i), self.dexp(*t)],
                    ));
                }
                self.list(span, items)
            }
            Fx::SumOf { tags, types } => self.tagged(span, "sumof", tags, types),
            Fx::ProductOf { tags, types } => self.tagged(span, "productof", tags, types),
            Fx::DApp { rator, rands } => {
                let mut items = vec![self.dexp(*rator)];
                items.extend(rands.iter().map(|r| self.dexp(*r)));
                self.list(span, items)
            }
            other => self.word(span, &format!("#<not-a-description:{}>", crate::sugar::head_name(other))),
        }
    }

    fn tagged(
        &self,
        span: Span,
        head: &str,
        tags: &[fixpt_read::Sym],
        types: &[FxId],
    ) -> Syntax {
        let mut items = vec![self.word(span, head)];
        for (t, ty) in tags.iter().zip(types) {
            items.push(self.list(
                span,
                vec![self.word(span, self.interner.name(*t)), self.dexp(*ty)],
            ));
        }
        self.list(span, items)
    }

    fn kind_bindings(&self, span: Span, ids: &[FxId], kinds: &[Kind]) -> Syntax {
        let bindings: Vec<Syntax> = ids
            .iter()
            .zip(kinds)
            .map(|(i, k)| self.list(span, vec![self.dexp(*i), self.kind(span, k)]))
            .collect();
        self.list(span, bindings)
    }

    /// A unification variable has no source syntax, so it prints under a name
    /// that could not be written: `*UNIF*-<n>`.
    fn variable(&self, id: FxId) -> Syntax {
        let span = self.span(id);
        let Some(v) = self.arena.var(id) else {
            return self.word(span, "#<not-a-variable>");
        };
        if v.is_unification() {
            return self.word(span, &format!("*UNIF*-{}", v.name));
        }
        if self.full_names {
            return self.word(span, &format!("{}-{}", self.interner.name(v.user_name), v.name));
        }
        self.word(span, self.interner.name(v.user_name))
    }

    pub fn exp(&self, id: FxId) -> Syntax {
        let span = self.span(id);
        // A literal prints as its value, not as the witness variable it parses
        // into.
        if let Some(lit) = &self.arena.exp_info(id).literal {
            return match lit {
                LiteralValue::SelfEvaluating(s) | LiteralValue::Sexp(s) => s.clone(),
            };
        }
        match self.arena.get(id) {
            Fx::Variable(_) => self.variable(id),
            Fx::Unparsed { syntax, .. } => {
                self.list(span, vec![self.word(span, "*unparsed*"), syntax.clone()])
            }
            Fx::Lambda { ids, types, user_types, body } => {
                let bindings: Vec<Syntax> = ids
                    .iter()
                    .zip(types)
                    .zip(user_types)
                    .map(|((i, t), present)| {
                        if *present {
                            self.list(span, vec![self.exp(*i), self.dexp(*t)])
                        } else {
                            self.exp(*i)
                        }
                    })
                    .collect();
                self.list(
                    span,
                    vec![self.word(span, "lambda"), self.list(span, bindings), self.exp(*body)],
                )
            }
            Fx::Let { ids, exps, body } => {
                let bindings: Vec<Syntax> = ids
                    .iter()
                    .zip(exps)
                    .map(|(i, e)| self.list(span, vec![self.exp(*i), self.exp(*e)]))
                    .collect();
                self.list(
                    span,
                    vec![self.word(span, "let"), self.list(span, bindings), self.exp(*body)],
                )
            }
            Fx::PLambda { ids, kinds, body } => {
                let bindings = self.kind_bindings(span, ids, kinds);
                self.list(span, vec![self.word(span, "plambda"), bindings, self.exp(*body)])
            }
            Fx::Proj { exp, descs } => {
                let mut items = vec![self.word(span, "proj"), self.exp(*exp)];
                items.extend(descs.iter().map(|d| self.dexp(*d)));
                self.list(span, items)
            }
            Fx::Module { text, .. } if self.original_module_text => text.clone(),
            Fx::Module { .. } => self.word(span, "(module ...)"),
            Fx::With { module, body, .. } => self.list(
                span,
                vec![self.word(span, "with"), self.exp(*module), self.exp(*body)],
            ),
            Fx::Extend { module, body, .. } => self.list(
                span,
                vec![self.word(span, "extend"), self.exp(*module), self.exp(*body)],
            ),
            Fx::If { test, then, els } => self.list(
                span,
                vec![
                    self.word(span, "if"),
                    self.exp(*test),
                    self.exp(*then),
                    self.exp(*els),
                ],
            ),
            Fx::Open(e) => self.list(span, vec![self.word(span, "open"), self.exp(*e)]),
            Fx::Close(e) => self.list(span, vec![self.word(span, "close"), self.exp(*e)]),
            Fx::Begin(exps) => {
                let mut items = vec![self.word(span, "begin")];
                items.extend(exps.iter().map(|e| self.exp(*e)));
                self.list(span, items)
            }
            Fx::Load { path, .. } => self.list(
                span,
                vec![self.word(span, "load"), Syntax::new(span, Datum::Str(path.clone()))],
            ),
            Fx::The { ty, exp } => self.list(
                span,
                vec![self.word(span, "the"), self.dexp(*ty), self.exp(*exp)],
            ),
            Fx::Does { effect, exp } => self.list(
                span,
                vec![self.word(span, "does"), self.dexp(*effect), self.exp(*exp)],
            ),
            Fx::Sum { ty, tag, exp } => self.list(
                span,
                vec![
                    self.word(span, "sum"),
                    self.dexp(*ty),
                    self.word(span, self.interner.name(*tag)),
                    self.exp(*exp),
                ],
            ),
            Fx::Product { ty, exps } => {
                let mut items = vec![self.word(span, "product"), self.dexp(*ty)];
                items.extend(exps.iter().map(|e| self.exp(*e)));
                self.list(span, items)
            }
            Fx::TagCase { ty, exp, tag, success, failure } => self.list(
                span,
                vec![
                    self.word(span, "tagcase"),
                    self.dexp(*ty),
                    self.exp(*exp),
                    self.word(span, self.interner.name(*tag)),
                    self.exp(*success),
                    self.exp(*failure),
                ],
            ),
            Fx::Extract { ty, exp, tag } => self.list(
                span,
                vec![
                    self.word(span, "extract"),
                    self.dexp(*ty),
                    self.exp(*exp),
                    self.word(span, self.interner.name(*tag)),
                ],
            ),
            Fx::App { rator, rands } => {
                let mut items = vec![self.exp(*rator)];
                items.extend(rands.iter().map(|r| self.exp(*r)));
                self.list(span, items)
            }
            other => {
                self.word(span, &format!("#<not-an-expression:{}>", crate::sugar::head_name(other)))
            }
        }
    }

    /// Render to the text the goldens contain.
    ///
    /// Words are carried as string data so that printing needs no mutable
    /// interner; this is where they lose their quotes again. Genuine strings
    /// in the source — `load`'s path — keep theirs, which is why they are
    /// marked rather than guessed at.
    pub fn render(&self, s: &Syntax) -> String {
        let mut out = String::new();
        self.put(s, &mut out);
        out
    }

    fn put(&self, s: &Syntax, out: &mut String) {
        match &s.datum {
            Datum::Str(text) => out.push_str(text),
            Datum::Nil => out.push_str("()"),
            Datum::List { items, tail } => {
                out.push('(');
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        out.push(' ');
                    }
                    self.put(item, out);
                }
                if let Some(t) = tail {
                    out.push_str(" . ");
                    self.put(t, out);
                }
                out.push(')');
            }
            _ => out.push_str(&fixpt_read::write_syntax(s, self.interner)),
        }
    }
}
