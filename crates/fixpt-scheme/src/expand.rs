//! The Scheme expander: [`Syntax`] to Core IR.
//!
//! Derived forms are handled the way `sugar.scm` and FX-91's `parse-cond`
//! handle theirs — by *rewriting to simpler syntax and re-expanding* rather
//! than by emitting IR directly. `(cond (a b) rest…)` becomes the syntax
//! `(if a b (cond rest…))` and goes back through [`Expander::expr`]. That keeps
//! each derived form to a few lines, keeps its semantics visibly equal to its
//! definition in the report, and means a bug fixed in `if` is fixed everywhere.
//!
//! Derived forms are native, which is what most Schemes do for them in
//! practice anyway. User macros are `syntax-rules` ([`crate::macros`]).
//!
//! # Hygiene
//!
//! Clinger & Rees's renaming, as in Larceny's Twobit. When syntax is
//! *constructed* — by a derived form here, or by a macro's template — the
//! identifiers it inserts are **aliases**: fresh symbols that no source text
//! can spell ([`Interner::uninterned`]), each recording the identifier it
//! stands for and the scopes in which that identifier should be looked up.
//! [`Expander::resolve`] looks an alias up as itself first — a binding form in
//! the same expansion may have bound it — and otherwise as its original, in
//! the scopes where the construct that inserted it was defined.
//!
//! An alias has its original's *name*. So everything that works by name —
//! `quote`, global variables, error messages, procedure names — sees the
//! original with no stripping pass, and only resolution sees the difference.

use crate::env::{Binding, Env, Special};
use std::collections::HashMap;
use fixpt_core::ir::{Builder, Node, NodeId, Program};
use fixpt_core::{GlobalId, VarId};
use fixpt_heap::Value;
use fixpt_read::{Datum, Interner, Num, Span, Sym, Syntax};
use fixpt_runtime::Runtime;

#[derive(Clone, Debug)]
pub struct ExpandError {
    pub span: Span,
    pub message: String,
}

impl ExpandError {
    pub(crate) fn at(span: Span, message: impl Into<String>) -> ExpandError {
        ExpandError { span, message: message.into() }
    }
}

impl std::fmt::Display for ExpandError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.message)
    }
}

type R<T> = Result<T, ExpandError>;

/// Where an alias resolves when nothing in its own expansion bound it.
#[derive(Copy, Clone, Debug)]
pub struct Alias {
    /// The identifier it stands for — itself possibly an alias, when a macro's
    /// template came from another macro's expansion.
    pub original: Sym,
    /// How many scopes, from the outermost, were visible where the inserting
    /// construct was defined; or [`CORE_SCOPE`].
    pub scope: u32,
}

/// The scope of the expander's own derived forms: a fixed table in which `if`
/// is always the special form, whatever a program has rebound.
pub const CORE_SCOPE: u32 = u32::MAX;

/// Symbols the expander needs to *construct*, cached once.
///
/// Every one is an alias resolved in the core environment, which is what makes
/// the derived forms hygienic: `cond`'s `if` is the special form even inside
/// `(let ((if list)) …)`.
pub struct Syms {
    pub(crate) quote: Sym,
    pub(crate) quasiquote: Sym,
    pub(crate) unquote: Sym,
    pub(crate) if_: Sym,
    pub(crate) lambda: Sym,
    pub(crate) begin: Sym,
    pub(crate) let_: Sym,
    pub(crate) letrec_star: Sym,
    pub(crate) cond: Sym,
    pub(crate) else_: Sym,
    pub(crate) define: Sym,
    pub(crate) and: Sym,
    pub(crate) or: Sym,
    pub(crate) cons: Sym,
    pub(crate) append: Sym,
    pub(crate) list: Sym,
    pub(crate) list_to_vector: Sym,
    pub(crate) memv: Sym,
    pub(crate) apply: Sym,
    pub(crate) values: Sym,
    pub(crate) call_with_values: Sym,
    pub(crate) call_cc: Sym,
    pub(crate) with_exception_handler: Sym,
    pub(crate) raise_continuable: Sym,
    pub(crate) make_record_type: Sym,
    pub(crate) record: Sym,
    pub(crate) record_of_type: Sym,
    pub(crate) record_ref: Sym,
    pub(crate) record_set: Sym,
    pub(crate) let_star: Sym,
    pub(crate) let_values: Sym,
    pub(crate) make_promise_thunk: Sym,
    pub(crate) wcm: Sym,
    pub(crate) make_promise_lazy: Sym,
    pub(crate) list_ref: Sym,
    pub(crate) tmp_rest: Sym,
}

impl Syms {
    fn new(i: &mut Interner, aliases: &mut HashMap<Sym, Alias>) -> Syms {
        let mut core = |name: &str| {
            let original = i.intern(name);
            let a = i.uninterned(name);
            aliases.insert(a, Alias { original, scope: CORE_SCOPE });
            a
        };
        let i = &mut core;
        Syms {
            quote: i("quote"),
            quasiquote: i("quasiquote"),
            unquote: i("unquote"),
            if_: i("if"),
            lambda: i("lambda"),
            begin: i("begin"),
            let_: i("let"),
            letrec_star: i("letrec*"),
            cond: i("cond"),
            else_: i("else"),
            define: i("define"),
            and: i("and"),
            or: i("or"),
            cons: i("cons"),
            append: i("append"),
            list: i("list"),
            list_to_vector: i("list->vector"),
            memv: i("memv"),
            apply: i("apply"),
            values: i("values"),
            call_with_values: i("call-with-values"),
            call_cc: i("call-with-current-continuation"),
            with_exception_handler: i("with-exception-handler"),
            raise_continuable: i("raise-continuable"),
            make_record_type: i("%make-record-type"),
            record: i("%record"),
            record_of_type: i("%record-of-type?"),
            record_ref: i("%record-ref"),
            record_set: i("%record-set!"),
            let_star: i("let*"),
            let_values: i("let-values"),
            make_promise_thunk: i("%make-promise-thunk"),
            wcm: i("%wcm"),
            make_promise_lazy: i("%make-promise-lazy"),
            list_ref: i("list-ref"),
            tmp_rest: i(" values-rest"),
        }
    }
}

/// Expander state that outlives one input: the arena, the top-level scope, the
/// cached symbols and the gensym counter.
pub struct ExpanderParts {
    pub builder: Builder,
    pub env: Env,
    pub syms: Syms,
    pub gensym_counter: u32,
    pub aliases: HashMap<Sym, Alias>,
    pub core: HashMap<Sym, Binding>,
    pub macros: Vec<std::rc::Rc<crate::macros::Macro>>,
}

pub struct Expander<'a> {
    pub(crate) rt: &'a mut Runtime,
    pub(crate) b: Builder,
    pub(crate) env: Env,
    pub(crate) syms: Syms,
    /// Counter behind [`Expander::gensym`]. Without user macros the only
    /// capture risk is an expansion shadowing a user binding, which unique
    /// names rule out.
    pub(crate) gensym_counter: u32,
    /// Every alias made so far. Kept across inputs: an alias defined at the top
    /// level by one input can be referred to by the next.
    pub(crate) aliases: HashMap<Sym, Alias>,
    /// The core environment: the special forms, by their plain names.
    pub(crate) core: HashMap<Sym, Binding>,
    /// Macros, indexed by [`Binding::Macro`].
    pub(crate) macros: Vec<std::rc::Rc<crate::macros::Macro>>,
    /// How many macro uses are being expanded inside one another.
    pub(crate) macro_depth: u32,
}

const SPECIAL_FORMS: &[(&str, Special)] = &[
    ("quote", Special::Quote),
    ("quasiquote", Special::Quasiquote),
    ("unquote", Special::Unquote),
    ("unquote-splicing", Special::UnquoteSplicing),
    ("if", Special::If),
    ("lambda", Special::Lambda),
    ("define", Special::Define),
    ("define-values", Special::DefineValues),
    ("define-record-type", Special::DefineRecordType),
    ("set!", Special::Set),
    ("begin", Special::Begin),
    ("let", Special::Let),
    ("let*", Special::LetStar),
    ("letrec", Special::Letrec),
    ("letrec*", Special::LetrecStar),
    ("let-values", Special::LetValues),
    ("let*-values", Special::LetStarValues),
    ("do", Special::Do),
    ("cond", Special::Cond),
    ("case", Special::Case),
    ("and", Special::And),
    ("or", Special::Or),
    ("when", Special::When),
    ("unless", Special::Unless),
    ("delay", Special::Delay),
    ("delay-force", Special::DelayForce),
    ("make-promise", Special::Delay),
    ("guard", Special::Guard),
    ("with-continuation-mark", Special::WithMark),
    ("define-syntax", Special::DefineSyntax),
    ("let-syntax", Special::LetSyntax),
    ("letrec-syntax", Special::LetrecSyntax),
    ("syntax-rules", Special::SyntaxRules),
    ("else", Special::Else),
    ("=>", Special::Arrow),
];

impl<'a> Expander<'a> {
    pub fn new(rt: &'a mut Runtime) -> Expander<'a> {
        let mut aliases = HashMap::new();
        let syms = Syms::new(&mut rt.interner, &mut aliases);
        let mut env = Env::new();
        let mut core = HashMap::new();
        for (name, s) in SPECIAL_FORMS {
            // `make-promise` is both a primitive and, here, a special form: the
            // primitive is what `delay` ultimately calls, and binding the name
            // as special would shadow it, so it is deliberately left out of the
            // table above except as an alias. See `expand_delay`.
            if *name == "make-promise" {
                continue;
            }
            let sym = rt.interner.intern(name);
            env.bind_top(sym, Binding::Special(*s));
            core.insert(sym, Binding::Special(*s));
        }
        Expander {
            rt,
            b: Builder::new(),
            env,
            syms,
            gensym_counter: 0,
            aliases,
            core,
            macros: Vec::new(),
            macro_depth: 0,
        }
    }

    /// Resume expansion with state carried over from an earlier call — how a
    /// REPL keeps its top-level bindings and its arena across inputs.
    pub fn resume(rt: &'a mut Runtime, parts: ExpanderParts) -> Expander<'a> {
        Expander {
            rt,
            b: parts.builder,
            env: parts.env,
            syms: parts.syms,
            gensym_counter: parts.gensym_counter,
            aliases: parts.aliases,
            core: parts.core,
            macros: parts.macros,
            macro_depth: 0,
        }
    }

    pub fn into_parts(self, body: NodeId) -> (Program, ExpanderParts) {
        let Expander { b, env, syms, gensym_counter, aliases, core, macros, .. } = self;
        let program = b.finish(body);
        (
            program,
            ExpanderParts { builder: Builder::new(), env, syms, gensym_counter, aliases, core, macros },
        )
    }

    /// Expand top-level forms into the current arena and return the body node.
    pub fn expand_forms(&mut self, forms: &[Syntax]) -> R<NodeId> {
        let span = forms
            .first()
            .map(|f| f.span)
            .unwrap_or(Span::new(fixpt_read::FileId(0), 0, 0));
        let mut nodes = Vec::new();
        for form in forms {
            nodes.push(self.top_level(form)?);
        }
        Ok(self.seq(span, nodes))
    }

    /// Expand a whole top-level program.
    pub fn expand_program(&mut self, forms: &[Syntax]) -> R<Program> {
        let span = forms
            .first()
            .map(|f| f.span)
            .unwrap_or(Span::new(fixpt_read::FileId(0), 0, 0));
        let mut nodes = Vec::new();
        for form in forms {
            nodes.push(self.top_level(form)?);
        }
        let body = self.seq(span, nodes);
        let builder = std::mem::replace(&mut self.b, Builder::new());
        let mut program = builder.finish(body);
        fixpt_core::analyze(&mut program);
        Ok(program)
    }

    /// A top-level form. `define` here creates a global, not a local binding.
    pub(crate) fn top_level(&mut self, form: &Syntax) -> R<NodeId> {
        // A macro use is expanded first and its result treated as a top-level
        // form in its own right, so a macro can expand into definitions.
        if let Some(out) = self.expand_head_macro(form)? {
            return self.nested(|e| e.top_level(&out));
        }
        if let Some(items) = form.as_proper_list()
            && let Some(head) = items.first().and_then(|h| h.as_symbol())
            && self.resolve(head) == Some(Binding::Special(Special::DefineSyntax))
        {
            let (name, spec) = self.split_define_syntax(form, items)?;
            // Visible at the top level only: a top-level macro's free
            // identifiers mean what they mean at the top level.
            let id = self.make_macro(name, &spec, 1)?;
            self.env.bind_top(name, Binding::Macro(id));
            return self.constant(form.span, Value::UNSPECIFIED);
        }
        // `define-record-type` and `define-values` are definition *groups*:
        // they stand for several `define`s. Rewriting them before the
        // define-scan is what lets them work identically at the top level and
        // at the head of a body, without either site knowing about them.
        if let Some(forms) = self.definition_group(form)? {
            let mut nodes = Vec::new();
            for f in &forms {
                nodes.push(self.top_level(f)?);
            }
            return Ok(self.seq(form.span, nodes));
        }
        if let Some(items) = form.as_proper_list()
            && let Some(head) = items.first().and_then(|h| h.as_symbol())
            && self.resolve(head) == Some(Binding::Special(Special::Define))
        {
            return self.top_level_define(form, items);
        }
        if let Some(items) = form.as_proper_list()
            && let Some(head) = items.first().and_then(|h| h.as_symbol())
            && self.resolve(head) == Some(Binding::Special(Special::Begin))
        {
            // An annotated expression is *not* a sequence, so it must be
            // recognised before the splice — otherwise a top-level
            // `(begin '(%fx-note …) e)` is torn into two top-level forms and
            // the metadata is discarded. That is exactly where it matters: an
            // FX front end's erased forms arrive at the top level.
            let args = &items[1..];
            if let Some(facts) = self.read_note(args)
                && args.len() == 2
            {
                let node = self.top_level(&args[1])?;
                self.b.set_facts(node, facts);
                return Ok(node);
            }
            // `(begin ...)` at top level splices, so its `define`s are also
            // top-level definitions rather than internal ones.
            let mut nodes = Vec::new();
            for f in &items[1..] {
                nodes.push(self.top_level(f)?);
            }
            return Ok(self.seq(form.span, nodes));
        }
        self.expr(form)
    }

    /// `(define-syntax name spec)`.
    pub(crate) fn split_define_syntax(&self, form: &Syntax, items: &[Syntax]) -> R<(Sym, Syntax)> {
        match items {
            [_, name, spec] => {
                let name = name
                    .as_symbol()
                    .ok_or_else(|| ExpandError::at(name.span, "`define-syntax` needs a name"))?;
                Ok((name, spec.clone()))
            }
            _ => Err(ExpandError::at(form.span, "`define-syntax` takes a name and a transformer")),
        }
    }

    fn top_level_define(&mut self, form: &Syntax, items: &[Syntax]) -> R<NodeId> {
        let (name, value) = self.split_define(form, items)?;
        let g = self.global(name);
        let init = self.named_expr(&value, Some(name))?;
        Ok(self.b.node(form.span, Node::GlobalSet(g, init)))
    }

    /// `(define x e)` and `(define (f a…) body…)` and the dotted variants,
    /// reduced to a name and an expression.
    pub(crate) fn split_define(&mut self, form: &Syntax, items: &[Syntax]) -> R<(Sym, Syntax)> {
        if items.len() < 2 {
            return Err(ExpandError::at(form.span, "`define` needs a name"));
        }
        match &items[1].datum {
            Datum::Symbol(name) => {
                let value = match items.len() {
                    2 => Syntax::new(form.span, Datum::Bool(false)),
                    3 => items[2].clone(),
                    _ => return Err(ExpandError::at(form.span, "`define` takes at most one value")),
                };
                Ok((*name, value))
            }
            // `(define (f . formals) body…)` => `(define f (lambda formals body…))`
            Datum::List { items: head, tail } => {
                let name = head
                    .first()
                    .and_then(|h| h.as_symbol())
                    .ok_or_else(|| ExpandError::at(items[1].span, "`define` needs a name"))?;
                let formals = Syntax::new(
                    items[1].span,
                    Datum::List { items: head[1..].to_vec(), tail: tail.clone() },
                );
                let mut lam = vec![Syntax::symbol(form.span, self.syms.lambda), formals];
                lam.extend_from_slice(&items[2..]);
                Ok((name, Syntax::list(form.span, lam)))
            }
            _ => Err(ExpandError::at(items[1].span, "`define` needs a name")),
        }
    }

    // ------------------------------------------------------------ expressions
    pub fn expr(&mut self, s: &Syntax) -> R<NodeId> {
        self.named_expr(s, None)
    }

    /// `name` is used to label a lambda for backtraces; it does not affect
    /// scoping.
    pub(crate) fn named_expr(&mut self, s: &Syntax, name: Option<Sym>) -> R<NodeId> {
        match &s.datum {
            Datum::Bool(b) => self.constant(s.span, Value::boolean(*b)),
            Datum::Char(c) => self.constant(s.span, Value::char(*c)),
            Datum::Nil => self.constant(s.span, Value::NULL),
            Datum::Number(n) => {
                let v = fixpt_runtime::num_from_literal(self.rt, n);
                self.constant(s.span, v)
            }
            Datum::Str(text) => {
                let v = self.rt.heap.make_string(text);
                self.constant(s.span, v)
            }
            Datum::Vector(_) | Datum::Bytevector(_) => {
                let v = self.datum_to_value(s);
                self.constant(s.span, v)
            }
            Datum::Symbol(sym) => self.variable(s.span, *sym),
            Datum::List { items, tail } => {
                if tail.is_some() {
                    return Err(ExpandError::at(s.span, "a dotted list is not an expression"));
                }
                self.combination(s, items, name)
            }
        }
    }

    pub(crate) fn combination(&mut self, s: &Syntax, items: &[Syntax], name: Option<Sym>) -> R<NodeId> {
        if items.is_empty() {
            return Err(ExpandError::at(s.span, "`()` is not an expression"));
        }
        if let Some(head) = items[0].as_symbol() {
            match self.resolve(head) {
                Some(Binding::Special(sp)) => return self.special(s, sp, items, name),
                Some(Binding::Macro(id)) => {
                    let out = self.expand_macro(id, s)?;
                    return self.nested(|e| e.named_expr(&out, name));
                }
                _ => {}
            }
        }
        let rator = self.expr(&items[0])?;
        let mut rands = Vec::with_capacity(items.len() - 1);
        for a in &items[1..] {
            rands.push(self.expr(a)?);
        }
        Ok(self.b.node(s.span, Node::App { rator, rands: rands.into_boxed_slice() }))
    }

    pub(crate) fn variable(&mut self, span: Span, sym: Sym) -> R<NodeId> {
        match self.resolve(sym) {
            Some(Binding::Local(v)) => Ok(self.b.node(span, Node::Ref(v))),
            Some(Binding::Global(g)) => Ok(self.b.node(span, Node::GlobalRef(g))),
            Some(Binding::Special(_) | Binding::Macro(_)) => {
                let name = self.rt.interner.name(sym).to_string();
                Err(ExpandError::at(span, format!("`{name}` is syntax, not a variable")))
            }
            // An unbound reference is not an expansion error: Scheme resolves
            // globals at run time, so forward references between top-level
            // definitions have to work.
            None => {
                let g = self.global(sym);
                Ok(self.b.node(span, Node::GlobalRef(g)))
            }
        }
    }

    /// What an identifier means here. See the module docs on hygiene.
    pub(crate) fn resolve(&self, sym: Sym) -> Option<Binding> {
        self.resolve_within(sym, usize::MAX)
    }

    /// What an identifier means in the outermost `limit` scopes: how a macro
    /// looks up its literals in the environment it was defined in.
    pub(crate) fn resolve_within(&self, mut sym: Sym, mut limit: usize) -> Option<Binding> {
        loop {
            if let Some(b) = self.env.lookup_within(sym, limit) {
                return Some(b);
            }
            let a = *self.aliases.get(&sym)?;
            if a.scope == CORE_SCOPE {
                return self.core.get(&a.original).copied();
            }
            sym = a.original;
            limit = a.scope as usize;
        }
    }

    /// A fresh alias for `original`, resolving in the outermost `scope` scopes.
    pub(crate) fn alias(&mut self, original: Sym, scope: u32) -> Sym {
        let name = self.rt.interner.name(original).to_string();
        let a = self.rt.interner.uninterned(&name);
        self.aliases.insert(a, Alias { original, scope });
        a
    }

    pub(crate) fn global(&mut self, sym: Sym) -> GlobalId {
        let name = self.rt.interner.name(sym).to_string();
        let s = self.rt.heap.intern(&name);
        let slot = self.rt.heap.symbol_global_slot(s);
        let g = GlobalId(slot as u32);
        self.env.bind_top(sym, Binding::Global(g));
        g
    }

    pub(crate) fn constant(&mut self, span: Span, v: Value) -> R<NodeId> {
        let c = self.b.constant(v);
        Ok(self.b.node(span, Node::Const(c)))
    }

    pub(crate) fn seq(&mut self, span: Span, mut nodes: Vec<NodeId>) -> NodeId {
        match nodes.len() {
            0 => {
                let c = self.b.constant(Value::UNSPECIFIED);
                self.b.node(span, Node::Const(c))
            }
            1 => nodes.pop().expect("length checked"),
            _ => self.b.node(span, Node::Seq(nodes.into_boxed_slice())),
        }
    }

    // --------------------------------------------------------------- bodies
    /// A `<body>`: internal definitions, then expressions. R7RS says the
    /// definitions are `letrec*`-scoped, so that is literally what this builds.
    ///
    /// The leading forms are scanned one at a time, because whether a form is a
    /// definition can depend on expanding it: a macro use may produce a
    /// `define`, a `begin` of definitions, or another macro use. Each name is
    /// bound as it is found, and a `define-syntax` is in scope for the rest of
    /// the body. The first form that is none of these ends the definitions.
    pub(crate) fn body(&mut self, span: Span, forms: &[Syntax]) -> R<NodeId> {
        if forms.is_empty() {
            return Err(ExpandError::at(span, "an empty body has no value"));
        }
        self.env.push();
        let result = self.body_in_scope(span, forms);
        self.env.pop();
        result
    }

    fn body_in_scope(&mut self, span: Span, forms: &[Syntax]) -> R<NodeId> {
        let mut queue: std::collections::VecDeque<Syntax> = forms.iter().cloned().collect();
        let mut defs: Vec<(Sym, Syntax, VarId)> = Vec::new();
        let mut exprs: Vec<Syntax> = Vec::new();
        let mut expansions = 0u32;
        while let Some(form) = queue.pop_front() {
            if let Some(out) = self.expand_head_macro(&form)? {
                expansions += 1;
                if expansions > crate::macros::MAX_EXPANSION_DEPTH {
                    return Err(ExpandError::at(form.span, "macro expansion in a body does not terminate"));
                }
                queue.push_front(out);
                continue;
            }
            if let Some(group) = self.definition_group(&form)? {
                for f in group.into_iter().rev() {
                    queue.push_front(f);
                }
                continue;
            }
            let head = form
                .as_proper_list()
                .and_then(|it| it.first())
                .and_then(|h| h.as_symbol())
                .and_then(|h| self.resolve(h));
            match head {
                Some(Binding::Special(Special::Define)) => {
                    let items = form.as_proper_list().expect("checked above");
                    let (name, value) = self.split_define(&form, items)?;
                    let v = self.b.var(name, span);
                    self.env.bind(name, Binding::Local(v));
                    defs.push((name, value, v));
                }
                Some(Binding::Special(Special::DefineSyntax)) => {
                    let items = form.as_proper_list().expect("checked above");
                    let (name, spec) = self.split_define_syntax(&form, items)?;
                    // In scope in its own definition, like `letrec-syntax`.
                    let id = self.make_macro(name, &spec, self.env.depth() as u32)?;
                    self.env.bind(name, Binding::Macro(id));
                }
                // `(begin def …)` in a body splices its definitions — unless it
                // is an annotated expression, which is one form, not a group.
                Some(Binding::Special(Special::Begin))
                    if {
                        let args = &form.as_proper_list().expect("checked above")[1..];
                        !(args.len() == 2 && self.read_note(args).is_some())
                    } =>
                {
                    let items = form.as_proper_list().expect("checked above").to_vec();
                    for f in items[1..].iter().rev() {
                        queue.push_front(f.clone());
                    }
                }
                _ => {
                    exprs.push(form);
                    exprs.extend(queue.drain(..));
                    break;
                }
            }
            expansions = 0;
        }
        if defs.is_empty() {
            if exprs.is_empty() {
                return Err(ExpandError::at(span, "a body of only syntax definitions has no value"));
            }
            let mut nodes = Vec::with_capacity(exprs.len());
            for f in &exprs {
                nodes.push(self.expr(f)?);
            }
            return Ok(self.seq(span, nodes));
        }
        let mut inits = Vec::with_capacity(defs.len());
        for (name, value, _) in &defs {
            inits.push(self.named_expr(value, Some(*name))?);
        }
        let mut nodes = Vec::new();
        for f in &exprs {
            nodes.push(self.expr(f)?);
        }
        if nodes.is_empty() {
            return Err(ExpandError::at(span, "a body of only definitions has no value"));
        }
        let inner = self.seq(span, nodes);
        let vars: Vec<VarId> = defs.iter().map(|(_, _, v)| *v).collect();
        Ok(self.b.node(
            span,
            Node::Fix {
                vars: vars.into_boxed_slice(),
                inits: inits.into_boxed_slice(),
                body: inner,
            },
        ))
    }

    // -------------------------------------------------------- datum → value
    /// Quoted data become real heap objects, interned in the constant pool so
    /// that quoting the same datum twice yields `eq?` results.
    pub(crate) fn datum_to_value(&mut self, s: &Syntax) -> Value {
        match &s.datum {
            Datum::Bool(b) => Value::boolean(*b),
            Datum::Char(c) => Value::char(*c),
            Datum::Nil => Value::NULL,
            Datum::Number(n) => fixpt_runtime::num_from_literal(self.rt, n),
            Datum::Str(text) => self.rt.heap.make_string(text),
            Datum::Symbol(sym) => {
                let name = self.rt.interner.name(*sym).to_string();
                self.rt.heap.intern(&name)
            }
            Datum::List { items, tail } => {
                let mut acc = match tail {
                    Some(t) => self.datum_to_value(t),
                    None => Value::NULL,
                };
                for item in items.iter().rev() {
                    let v = self.datum_to_value(item);
                    acc = self.rt.heap.cons(v, acc);
                }
                acc
            }
            Datum::Vector(items) => {
                let vals: Vec<Value> = items.iter().map(|i| self.datum_to_value(i)).collect();
                self.rt.heap.vector_from(&vals)
            }
            Datum::Bytevector(bytes) => self.rt.heap.make_bytevector(bytes),
        }
    }

    /// A fresh symbol that no source text can name, for expansions that need a
    /// temporary (`or`, `cond` with `=>`, `case`, `do`, `guard`).
    pub(crate) fn gensym(&mut self, span: Span, prefix: &str) -> Syntax {
        self.gensym_counter += 1;
        let name = format!(" {prefix}.{}", self.gensym_counter);
        let s = self.rt.interner.intern(&name);
        Syntax::symbol(span, s)
    }
}

// ------------------------------------------------------- syntax building
// Free functions rather than methods: expansions interleave them with
// `gensym`, which needs `&mut self`, and a method taking `&self` cannot appear
// in the same argument list.

pub(crate) fn sym(span: Span, s: Sym) -> Syntax {
    Syntax::symbol(span, s)
}

pub(crate) fn form(span: Span, head: Sym, mut rest: Vec<Syntax>) -> Syntax {
    let mut items = vec![Syntax::symbol(span, head)];
    items.append(&mut rest);
    Syntax::list(span, items)
}

pub(crate) fn fixnum(span: Span, n: i64) -> Syntax {
    Syntax::new(span, Datum::Number(Num::Int(n)))
}

pub(crate) fn nil(span: Span) -> Syntax {
    Syntax::new(span, Datum::Nil)
}

// ------------------------------------------------------------- quasiquote

impl Expander<'_> {
    /// Expand `` `x `` into constructor calls, tracking nesting level so that
    /// an inner quasiquote's unquotes belong to it and not to the outer one.
    pub(crate) fn quasiquote(&mut self, s: &Syntax, level: u32) -> R<Syntax> {
        let span = s.span;
        match &s.datum {
            Datum::List { items, tail } => {
                // (unquote e) / (quasiquote e) at the head.
                if items.len() == 2
                    && tail.is_none()
                    && let Some(head) = items[0].as_symbol()
                {
                    {
                        let b = self.resolve(head);
                        if b == Some(Binding::Special(Special::Unquote)) {
                            if level == 1 {
                                return Ok(items[1].clone());
                            }
                            let inner = self.quasiquote(&items[1], level - 1)?;
                            return Ok(self.rebuild(span, self.syms.unquote, inner));
                        }
                        if b == Some(Binding::Special(Special::Quasiquote)) {
                            let inner = self.quasiquote(&items[1], level + 1)?;
                            return Ok(self.rebuild(span, self.syms.quasiquote, inner));
                        }
                    }
                }
                // Build the list right to left, splicing where asked.
                let mut acc = match tail {
                    Some(t) => self.quasiquote(t, level)?,
                    None => form(span, self.syms.quote, vec![nil(span)]),
                };
                for item in items.iter().rev() {
                    let splice = item.as_proper_list().and_then(|p| {
                        if p.len() == 2
                            && p[0].as_symbol().is_some_and(|h| {
                                self.resolve(h)
                                    == Some(Binding::Special(Special::UnquoteSplicing))
                            })
                        {
                            Some(p[1].clone())
                        } else {
                            None
                        }
                    });
                    acc = match splice {
                        Some(e) if level == 1 => form(span, self.syms.append, vec![e, acc]),
                        _ => {
                            let head = self.quasiquote(item, level)?;
                            form(span, self.syms.cons, vec![head, acc])
                        }
                    };
                }
                Ok(acc)
            }
            Datum::Vector(items) => {
                let as_list = Syntax::new(span, Datum::List { items: items.clone(), tail: None });
                let built = self.quasiquote(&as_list, level)?;
                Ok(form(span, self.syms.list_to_vector, vec![built]))
            }
            // Self-evaluating data need no quote, but quoting them is harmless
            // and keeps one path.
            _ => Ok(form(span, self.syms.quote, vec![s.clone()])),
        }
    }

    fn rebuild(&self, span: Span, head: Sym, inner: Syntax) -> Syntax {
        form(
            span,
            self.syms.list,
            vec![form(span, self.syms.quote, vec![sym(span, head)]), inner],
        )
    }

    /// `define-record-type` and `define-values` stand for several `define`s.
    /// Returns `None` for anything else.
    pub(crate) fn definition_group(&mut self, form_syn: &Syntax) -> R<Option<Vec<Syntax>>> {
        let Some(items) = form_syn.as_proper_list() else { return Ok(None) };
        let Some(head) = items.first().and_then(|h| h.as_symbol()) else { return Ok(None) };
        match self.resolve(head) {
            Some(Binding::Special(Special::DefineRecordType)) => {
                Ok(Some(self.record_type_defines(form_syn.span, &items[1..])?))
            }
            Some(Binding::Special(Special::DefineValues)) => {
                Ok(Some(self.define_values_defines(form_syn.span, &items[1..])?))
            }
            _ => Ok(None),
        }
    }

    /// `(define-values (a b) e)` becomes a temporary holding the value list and
    /// one `define` per name.
    fn define_values_defines(&mut self, span: Span, args: &[Syntax]) -> R<Vec<Syntax>> {
        if args.len() != 2 {
            return Err(ExpandError::at(span, "`define-values` takes formals and an expression"));
        }
        let tmp = self.gensym(span, "values");
        let producer = form(span, self.syms.lambda, vec![nil(span), args[1].clone()]);
        let collector = form(
            span,
            self.syms.lambda,
            vec![sym(span, self.syms.tmp_rest), sym(span, self.syms.tmp_rest)],
        );
        let cwv = form(span, self.syms.call_with_values, vec![producer, collector]);
        let mut out = vec![form(span, self.syms.define, vec![tmp.clone(), cwv])];

        let names = match &args[0].datum {
            Datum::Symbol(_) => {
                out.push(form(span, self.syms.define, vec![args[0].clone(), tmp]));
                return Ok(out);
            }
            Datum::Nil => Vec::new(),
            Datum::List { items, tail: None } => items.clone(),
            _ => {
                return Err(ExpandError::at(args[0].span, "`define-values` needs a list of names"));
            }
        };
        for (i, name) in names.iter().enumerate() {
            let idx = fixnum(span, i as i64);
            let accessor = form(span, self.syms.list_ref, vec![tmp.clone(), idx]);
            out.push(form(span, self.syms.define, vec![name.clone(), accessor]));
        }
        Ok(out)
    }
}

// ------------------------------------------------------ front-end metadata

/// Reading what another front end proved, out of the Scheme it emitted.
///
/// The encoding is Twobit's: a quoted constant in a position where its value is
/// discarded. `pass2.aux.sch` builds every lambda node as literal Scheme with
/// `'(R F G decls doc)` sitting in the body, so the analyses travel with the
/// code and any conforming evaluator ignores them. Here the same trick is
/// spelled
///
/// ```scheme
/// (begin '(%fx-note (pure) (because "int ! pure")) (+ x 1))
/// ```
///
/// which is an ordinary two-expression `begin`: the annotation is evaluated for
/// effect and thrown away. Three consequences, all of them the point:
///
/// * the emitted program stays runnable by **any** Scheme, so an FX front end
///   can be tested against a stock implementation;
/// * the metadata survives being written to text and read back, because it is
///   data rather than a side table someone has to remember to carry;
/// * a compiler that does not know about `%fx-note` produces correct code and
///   merely slower code, so adopting it is never a correctness risk.
///
/// What is added beyond Twobit is `because` and the basis. `lambda.F` says a
/// variable is free and nothing can ask why; a claim here records the evidence
/// and whether it was *checked* by a type system or merely inferred.
impl Expander<'_> {
    /// If `args[0]` is an annotation, the facts it asserts.
    pub(crate) fn read_note(&mut self, args: &[Syntax]) -> Option<fixpt_core::facts::Facts> {
        use fixpt_core::facts::{Basis, Claim, Fact, Facts};
        let quoted = self.quoted_datum(args.first()?)?;
        let Datum::List { items, tail: None } = quoted else { return None };
        let head = match items.first().map(|s| &s.datum) {
            Some(Datum::Symbol(s)) => *s,
            _ => return None,
        };
        if self.rt.interner.name(head) != "%fx-note" {
            return None;
        }
        let mut facts = Vec::new();
        let mut because: Option<String> = None;
        let mut basis = Basis::Checked;
        for item in &items[1..] {
            let Datum::List { items: parts, tail: None } = &item.datum else { continue };
            let Some(Datum::Symbol(tag)) = parts.first().map(|s| &s.datum) else { continue };
            match self.rt.interner.name(*tag) {
                "because" => {
                    because = parts.get(1).map(|s| {
                        fixpt_read::write_syntax(s, &self.rt.interner)
                    });
                }
                "basis" => {
                    if let Some(Datum::Symbol(b)) = parts.get(1).map(|s| &s.datum) {
                        basis = match self.rt.interner.name(*b) {
                            "inferred" => Basis::Inferred,
                            "asserted" => Basis::Asserted,
                            _ => Basis::Checked,
                        };
                    }
                }
                "pure" => facts.push(Claim::Pure),
                "no-escape" => facts.push(Claim::NoEscape),
                "integrable" => {
                    if let Some(Datum::Symbol(n)) = parts.get(1).map(|s| &s.datum) {
                        facts.push(Claim::Integrable(*n));
                    }
                }
                _ => {}
            }
        }
        Some(Facts(
            facts
                .into_iter()
                .map(|claim| Fact { claim, basis, because: because.clone() })
                .collect(),
        ))
    }

    /// The datum inside `(quote x)`, if this is one.
    fn quoted_datum<'a>(&self, s: &'a Syntax) -> Option<&'a Datum> {
        let Datum::List { items, tail: None } = &s.datum else { return None };
        if items.len() != 2 {
            return None;
        }
        match &items[0].datum {
            Datum::Symbol(q) if self.rt.interner.name(*q) == "quote" => Some(&items[1].datum),
            _ => None,
        }
    }
}
