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
use fixpt_read::{Interner, Span, Syntax};

/// The unparser's own output tree.
///
/// Not [`Syntax`]: building one would need a mutable interner just to name
/// `->` or `moduleof`, and — the reason this exists — `Syntax` gives no way to
/// distinguish a bare word from a string *literal*, so a `(load "file")` path
/// printed without its quotes.
#[derive(Clone, Debug)]
pub enum Out {
    /// Printed as-is.
    Word(String),
    /// Printed with quotes, as source.
    Str(String),
    /// Copied verbatim from the user's own syntax.
    Datum(Syntax),
    List(Vec<Out>),
}

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

    /// A bare word in the output. Symbol names go through the same escaping
    /// `write` applies, so a numeric tag such as a `productof` label prints as
    /// `|1|` rather than `1`.
    fn word(&self, _span: Span, name: &str) -> Out {
        Out::Word(fixpt_read::escape_symbol(name))
    }

    fn list(&self, _span: Span, items: Vec<Out>) -> Out {
        Out::List(items)
    }

    pub fn kind(&self, span: Span, k: &Kind) -> Out {
        match k {
            Kind::Type => self.word(span, "type"),
            Kind::Effect => self.word(span, "effect"),
            Kind::DFunc(ks) => {
                let mut items: Vec<Out> = vec![self.word(span, "->>")];
                items.extend(ks.iter().map(|k| self.kind(span, k)));
                self.list(span, items)
            }
        }
    }

    pub fn dexp(&self, id: FxId) -> Out {
        let span = self.span(id);
        match self.arena.get(id) {
            Fx::Variable(_) => self.variable(id),
            Fx::Unparsed { syntax, .. } => Out::Datum(syntax.clone()),
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
                let mut items: Vec<Out> = vec![self.word(span, "maxeff")];
                items.extend(effects.iter().map(|e| self.dexp(*e)));
                self.list(span, items)
            }
            // `subr` prints as `->`.
            Fx::Subr { effect, ids, types, body } => {
                let bindings: Vec<Out> = ids
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
                let mut items: Vec<Out> = vec![self.word(span, "moduleof")];
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
                let mut items: Vec<Out> = vec![self.dexp(*rator)];
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
    ) -> Out {
        let mut items: Vec<Out> = vec![self.word(span, head)];
        for (t, ty) in tags.iter().zip(types) {
            items.push(self.list(
                span,
                vec![self.word(span, self.interner.name(*t)), self.dexp(*ty)],
            ));
        }
        self.list(span, items)
    }

    fn kind_bindings(&self, span: Span, ids: &[FxId], kinds: &[Kind]) -> Out {
        let bindings: Vec<Out> = ids
            .iter()
            .zip(kinds)
            .map(|(i, k)| self.list(span, vec![self.dexp(*i), self.kind(span, k)]))
            .collect();
        self.list(span, bindings)
    }

    /// A unification variable has no source syntax, so it prints under a name
    /// that could not be written: `*UNIF*-<n>`.
    fn variable(&self, id: FxId) -> Out {
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

    pub fn exp(&self, id: FxId) -> Out {
        let span = self.span(id);
        // A literal prints as its value, not as the witness variable it parses
        // into.
        if let Some(lit) = &self.arena.exp_info(id).literal {
            return match lit {
                LiteralValue::SelfEvaluating(s) | LiteralValue::Sexp(s) => Out::Datum(s.clone()),
            };
        }
        match self.arena.get(id) {
            Fx::Variable(_) => self.variable(id),
            Fx::Unparsed { syntax, .. } => {
                self.list(span, vec![self.word(span, "*unparsed*"), Out::Datum(syntax.clone())])
            }
            Fx::Lambda { ids, types, user_types, body } => {
                let bindings: Vec<Out> = ids
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
                let bindings: Vec<Out> = ids
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
                let mut items: Vec<Out> = vec![self.word(span, "proj"), self.exp(*exp)];
                items.extend(descs.iter().map(|d| self.dexp(*d)));
                self.list(span, items)
            }
            Fx::Module { text: Some(text), .. } if self.original_module_text => Out::Datum(text.clone()),
            // No source text: rebuild the module from its parts, which is
            // what makes a substituted module print `->` where the user wrote
            // `subr`.
            Fx::Module {
                abs_ids,
                abs_kinds,
                abs_descs,
                desc_ids,
                desc_descs,
                define_ids,
                define_exps,
                typed_ids,
                typed_types,
                typed_exps,
                ..
            } => {
                let mut items = vec![self.word(span, "module")];
                for ((i, k), d) in abs_ids.iter().zip(abs_kinds).zip(abs_descs) {
                    items.push(self.list(
                        span,
                        vec![
                            self.word(span, "define-abstraction"),
                            self.dexp(*i),
                            self.kind(span, k),
                            self.dexp(*d),
                        ],
                    ));
                }
                for (i, d) in desc_ids.iter().zip(desc_descs) {
                    items.push(self.list(
                        span,
                        vec![self.word(span, "define-description"), self.dexp(*i), self.dexp(*d)],
                    ));
                }
                for (i, e) in define_ids.iter().zip(define_exps) {
                    items.push(self.list(
                        span,
                        vec![self.word(span, "define"), self.exp(*i), self.exp(*e)],
                    ));
                }
                for ((i, t), e) in typed_ids.iter().zip(typed_types).zip(typed_exps) {
                    items.push(self.list(
                        span,
                        vec![
                            self.word(span, "define-typed"),
                            self.exp(*i),
                            self.dexp(*t),
                            self.exp(*e),
                        ],
                    ));
                }
                self.list(span, items)
            }
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
                let mut items: Vec<Out> = vec![self.word(span, "begin")];
                items.extend(exps.iter().map(|e| self.exp(*e)));
                self.list(span, items)
            }
            Fx::Load { path, .. } => {
                self.list(span, vec![self.word(span, "load"), Out::Str(path.clone())])
            }
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
                let mut items: Vec<Out> = vec![self.word(span, "product"), self.dexp(*ty)];
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
                let mut items: Vec<Out> = vec![self.exp(*rator)];
                items.extend(rands.iter().map(|r| self.exp(*r)));
                self.list(span, items)
            }
            other => {
                self.word(span, &format!("#<not-an-expression:{}>", crate::sugar::head_name(other)))
            }
        }
    }

    /// Render to the text the goldens contain.
    pub fn render(&self, s: &Out) -> String {
        let mut out = String::new();
        self.put(s, &mut out);
        out
    }

    fn put(&self, s: &Out, out: &mut String) {
        match s {
            Out::Word(text) => out.push_str(text),
            Out::Str(text) => {
                out.push('"');
                out.push_str(text);
                out.push('"');
            }
            Out::Datum(d) => out.push_str(&fixpt_read::write_syntax(d, self.interner)),
            Out::List(items) => {
                if items.is_empty() {
                    out.push_str("()");
                    return;
                }
                out.push('(');
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        out.push(' ');
                    }
                    self.put(item, out);
                }
                out.push(')');
            }
        }
    }
}
