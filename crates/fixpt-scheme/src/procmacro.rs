//! Procedural macros: SRFI 211's `er-macro-transformer` and
//! `ir-macro-transformer`.
//!
//! A procedural transformer is a Scheme procedure, so expanding a use means
//! *running Scheme in the middle of expansion*. Three things make that safe
//! and hygienic here.
//!
//! **Running.** The transformer's expression is expanded, lowered and run when
//! its `define-syntax` is expanded, by the same engine that runs everything
//! else ([`Host`]). Nothing in the current input has run yet at that point, so
//! the expression is expanded against the top-level environment only: it may
//! use globals from earlier inputs and from `begin-for-syntax`, and a local
//! variable is reported as what it is — not yet in existence.
//!
//! **The collector.** While a transformer runs, the expander is holding a
//! half-built program whose constants are heap values outside any root set. So
//! collection is held off for the duration of the call
//! ([`Heap::inhibit_collection`](fixpt_heap::Heap::inhibit_collection)): the
//! heap grows instead, which never moves anything.
//!
//! **`rename`, `compare` and `inject`.** These must consult the expander's
//! environment, which no primitive can see. They are Scheme procedures that
//! call `%host`, which *pauses* the machine and hands the request to the
//! expander; the expander answers and resumes it. The expander stays in
//! control throughout — no callbacks from primitives into Rust state.
//!
//! **Identifiers.** A transformer sees plain lists, as ER and IR promise, and
//! identifiers cross into Scheme as symbols, so `symbol?`, `eq?` and `case`
//! work on them. An identifier whose identity is not just its name — an alias
//! from an enclosing macro, a renamed identifier, and, for IR, *every* input
//! identifier — crosses as an **uninterned** symbol with that name, so it is
//! `eq?` only to itself, and maps back to exactly the identifier it came from.
//! That is what keeps a macro's input hygienic when another macro produced it,
//! which is the case the R7RS-large draft's non-normative ER/IR get wrong.
//!
//! The IR discipline is mark-and-flip on plain lists: input identifiers are
//! marked on the way in (uninterned), so after the transformer returns, any
//! *bare* symbol in its output must have come from its own template, and is
//! renamed; marked ones map back to what the user wrote. `inject` makes a bare
//! symbol mean what it would at the use site.

use crate::expand::{ExpandError, Expander};
use crate::session::Engine;
use fixpt_core::ir::Builder;
use fixpt_engine::Prepared;
use fixpt_heap::{ObjType, Value};
use fixpt_read::{Datum, Span, Sym, Syntax};
use std::collections::HashMap;

type R<T> = Result<T, ExpandError>;

/// The engine the expander calls into, borrowed from the session for the
/// duration of one input's expansion.
pub struct Host<'a> {
    pub engine: &'a mut Engine,
    pub prepared: &'a mut Prepared,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum ProcKind {
    /// Explicit renaming: bare symbols in the output mean what they mean at
    /// the use site; the transformer renames what it inserts.
    Er,
    /// Implicit renaming: bare symbols in the output are renamed; the
    /// transformer injects what it means to capture.
    Ir,
}

pub struct ProcMacro {
    pub(crate) name: Sym,
    kind: ProcKind,
    /// Heap root holding the transformer procedure.
    root: usize,
    scope: u32,
}

/// One expansion's identifier bookkeeping.
struct Conv {
    kind: ProcKind,
    scope: u32,
    /// Identifiers given uninterned symbols, and back.
    heap_of: HashMap<Sym, Value>,
    sym_of: HashMap<u64, Sym>,
    /// Renamings made in this expansion, memoised: renaming `if` twice gives
    /// the same identifier.
    renamed: HashMap<Sym, Sym>,
    /// The input's lists, so that a subform the transformer passes through
    /// untouched comes back as the original syntax — spans, aliases and all.
    pairs: HashMap<u64, Syntax>,
    span: Span,
}

impl Expander<'_> {
    // ------------------------------------------------------------ definition
    /// A procedural macro from a transformer expression, which is evaluated
    /// now.
    pub(crate) fn make_proc_macro(&mut self, name: Sym, spec: &Syntax, scope: u32) -> R<ProcMacro> {
        let v = self.eval_now(spec, true)?;
        let rtd = self.global_value("%transformer");
        let is_transformer = rtd.is_some_and(|rtd| {
            self.rt.heap.is_a(v, ObjType::Record)
                && self.rt.heap.obj_len(v) == 3
                && self.rt.heap.obj_ref(v, 0) == rtd
        });
        if !is_transformer {
            return Err(ExpandError::at(
                spec.span,
                "a macro's transformer must be `syntax-rules`, `er-macro-transformer` or `ir-macro-transformer`",
            ));
        }
        let kind = match self.rt.heap.symbol_name(self.rt.heap.obj_ref(v, 1)).as_str() {
            "ir" => ProcKind::Ir,
            _ => ProcKind::Er,
        };
        let proc = self.rt.heap.obj_ref(v, 2);
        let root = self.rt.heap.push_root(proc);
        Ok(ProcMacro { name, kind, root, scope })
    }

    fn global_value(&mut self, name: &str) -> Option<Value> {
        let s = self.rt.heap.intern_existing(name)?;
        let v = self.rt.heap.global(self.rt.heap.symbol_global_slot(s));
        if v.is_unbound() { None } else { Some(v) }
    }

    /// Expand and run `form` now, as a top-level form, returning its value.
    ///
    /// With `top_only`, it is expanded seeing only the top-level scope — the
    /// right environment for a transformer expression, which runs before any
    /// local binding around it exists.
    pub(crate) fn eval_now(&mut self, form: &Syntax, top_only: bool) -> R<Value> {
        let span = form.span;
        if self.host.is_none() {
            return Err(ExpandError::at(
                span,
                "this needs to run code during expansion, which only a session can do",
            ));
        }
        let node = if top_only {
            let top = self.env.top_only();
            let saved = std::mem::replace(&mut self.env, top);
            let r = self.top_level(form);
            self.env = saved;
            r?
        } else {
            self.top_level(form)?
        };
        // Lower just this expression. `analyze` resets what it does not reach,
        // which is harmless: the whole input is analysed again before it runs.
        let builder = std::mem::replace(&mut self.b, Builder::new());
        let mut program = builder.finish(node);
        fixpt_core::analyze(&mut program);
        let host = self.host.as_mut().expect("checked above");
        let thunk = host.prepared.thunk_for(&mut self.rt.heap, &self.rt.interner, &program);
        self.b = Builder::from_program(program);
        let thunk = thunk.map_err(|e| ExpandError::at(span, e.to_string()))?;
        self.run_scheme(span, thunk, &[], None)
    }

    /// Call `f` with `args` on the host engine, answering any `%host` requests
    /// through `conv`. Collection is held off throughout: see the module docs.
    fn run_scheme(&mut self, span: Span, f: Value, args: &[Value], mut conv: Option<&mut Conv>) -> R<Value> {
        self.rt.heap.inhibit_collection();
        let result = self.run_scheme_inner(span, f, args, &mut conv);
        self.rt.heap.allow_collection();
        result
    }

    fn run_scheme_inner(&mut self, span: Span, f: Value, args: &[Value], conv: &mut Option<&mut Conv>) -> R<Value> {
        let host = self.host.as_mut().expect("callers check for a host");
        let mut outcome = host.engine.call(self.rt, host.prepared, f, args);
        loop {
            match outcome {
                Ok(v) => return Ok(v),
                Err(t) if t.suspended => {
                    let answer = match conv.as_deref_mut() {
                        Some(c) => self.answer(c, t.obj)?,
                        None => {
                            return Err(ExpandError::at(span, "`%host` called outside a macro transformer"));
                        }
                    };
                    let host = self.host.as_mut().expect("callers check for a host");
                    outcome = host.engine.answer_host(self.rt, host.prepared, answer);
                }
                Err(t) => {
                    let msg = self.describe_condition(t.obj);
                    return Err(ExpandError::at(span, msg));
                }
            }
        }
    }

    fn describe_condition(&self, obj: Value) -> String {
        let heap = &self.rt.heap;
        if self.rt.is_error_object(obj) {
            let msg = fixpt_runtime::display_value(heap, heap.obj_ref(obj, 1));
            let irritants = heap.list_to_vec(heap.obj_ref(obj, 2)).unwrap_or_default();
            if irritants.is_empty() {
                return msg;
            }
            let shown: Vec<String> = irritants.iter().map(|v| fixpt_runtime::write_value(heap, *v)).collect();
            return format!("{msg}: {}", shown.join(" "));
        }
        format!("uncaught: {}", fixpt_runtime::write_value(heap, obj))
    }

    // -------------------------------------------------------------- expansion
    pub(crate) fn expand_proc_macro(&mut self, pm: &ProcMacro, form: &Syntax) -> R<Syntax> {
        let mut conv = Conv {
            kind: pm.kind,
            scope: pm.scope,
            heap_of: HashMap::new(),
            sym_of: HashMap::new(),
            renamed: HashMap::new(),
            pairs: HashMap::new(),
            span: form.span,
        };
        let input = self.syntax_to_heap(form, &mut conv);
        let (first, compare) = match pm.kind {
            ProcKind::Er => ("%macro-rename", "%macro-compare"),
            ProcKind::Ir => ("%macro-inject", "%macro-compare"),
        };
        let (Some(first), Some(compare)) = (self.global_value(first), self.global_value(compare)) else {
            return Err(ExpandError::at(form.span, "procedural macros need the prelude"));
        };
        let f = self.rt.heap.root_at(pm.root);
        let out = self.run_scheme(form.span, f, &[input, first, compare], Some(&mut conv))?;
        self.heap_to_syntax(out, &mut conv).map_err(|what| {
            let n = self.rt.interner.name(pm.name).to_string();
            ExpandError::at(form.span, format!("`{n}` produced {what}, which is not syntax"))
        })
    }

    /// Answer one `%host` request: `(rename s)`, `(inject s)` or `(compare a b)`.
    fn answer(&mut self, c: &mut Conv, request: Value) -> R<Value> {
        let parts = self.rt.heap.list_to_vec(request).unwrap_or_default();
        let op = parts
            .first()
            .filter(|v| self.rt.heap.is_a(**v, ObjType::Symbol))
            .map(|v| self.rt.heap.symbol_name(*v))
            .unwrap_or_default();
        let is_sym = |e: &Self, v: Value| e.rt.heap.is_a(v, ObjType::Symbol);
        match (op.as_str(), &parts[1..]) {
            ("rename", [s]) if is_sym(self, *s) => {
                let original = self.plain_or_known(c, *s);
                let alias = self.renaming(c, original);
                Ok(self.marked(c, alias))
            }
            ("inject", [s]) if is_sym(self, *s) => {
                if !self.rt.heap.is_interned_symbol(*s) {
                    return Ok(*s);
                }
                let name = self.rt.heap.symbol_name(*s);
                let plain = self.rt.interner.intern(&name);
                Ok(self.marked(c, plain))
            }
            ("compare", [a, b]) => {
                if !(is_sym(self, *a) && is_sym(self, *b)) {
                    return Ok(Value::boolean(a == b));
                }
                let (x, y) = (self.identifier(c, *a), self.identifier(c, *b));
                Ok(Value::boolean(self.same_binding(x, y)))
            }
            _ => Err(ExpandError::at(
                c.span,
                format!("a macro transformer made a request its expander does not understand: {}",
                        fixpt_runtime::write_value(&self.rt.heap, request)),
            )),
        }
    }

    /// The renaming of `original` in this expansion — the same one each time.
    fn renaming(&mut self, c: &mut Conv, original: Sym) -> Sym {
        if let Some(a) = c.renamed.get(&original) {
            return *a;
        }
        let a = self.alias(original, c.scope);
        c.renamed.insert(original, a);
        a
    }

    /// The uninterned symbol standing for identifier `s` in this expansion.
    fn marked(&mut self, c: &mut Conv, s: Sym) -> Value {
        if let Some(v) = c.heap_of.get(&s) {
            return *v;
        }
        let name = self.rt.interner.name(s).to_string();
        let v = self.rt.heap.make_uninterned_symbol(&name);
        c.heap_of.insert(s, v);
        c.sym_of.insert(v.raw(), s);
        v
    }

    /// A heap symbol as the identifier it names *as data*: an uninterned one is
    /// the identifier it was made for; an interned one is the plain symbol.
    fn plain_or_known(&mut self, c: &Conv, v: Value) -> Sym {
        if let Some(s) = c.sym_of.get(&v.raw()) {
            return *s;
        }
        let name = self.rt.heap.symbol_name(v);
        self.rt.interner.intern(&name)
    }

    /// A heap symbol as the identifier it is *in the transformer's output*: an
    /// uninterned one is what it was made for; an interned one is a plain,
    /// use-site symbol under ER and a template-inserted, renamed one under IR.
    fn identifier(&mut self, c: &mut Conv, v: Value) -> Sym {
        if let Some(s) = c.sym_of.get(&v.raw()) {
            return *s;
        }
        let name = self.rt.heap.symbol_name(v);
        let plain = self.rt.interner.intern(&name);
        match c.kind {
            ProcKind::Er => plain,
            ProcKind::Ir => self.renaming(c, plain),
        }
    }

    // ------------------------------------------------------------ conversion
    fn syntax_to_heap(&mut self, s: &Syntax, c: &mut Conv) -> Value {
        match &s.datum {
            Datum::Bool(b) => Value::boolean(*b),
            Datum::Char(ch) => Value::char(*ch),
            Datum::Nil => Value::NULL,
            Datum::Number(n) => fixpt_runtime::num_from_literal(self.rt, n),
            Datum::Str(text) => self.rt.heap.make_string(text),
            Datum::Bytevector(b) => self.rt.heap.make_bytevector(b),
            Datum::Symbol(sym) => {
                // Under IR every input identifier is marked; under ER only
                // those whose identity is more than their name.
                if c.kind == ProcKind::Ir || self.aliases.contains_key(sym) {
                    self.marked(c, *sym)
                } else {
                    let name = self.rt.interner.name(*sym).to_string();
                    self.rt.heap.intern(&name)
                }
            }
            Datum::Vector(items) => {
                let vals: Vec<Value> = items.iter().map(|i| self.syntax_to_heap(i, c)).collect();
                self.rt.heap.vector_from(&vals)
            }
            Datum::List { items, tail } => {
                let mut acc = match tail {
                    Some(t) => self.syntax_to_heap(t, c),
                    None => Value::NULL,
                };
                for item in items.iter().rev() {
                    let v = self.syntax_to_heap(item, c);
                    acc = self.rt.heap.cons(v, acc);
                }
                c.pairs.insert(acc.raw(), s.clone());
                acc
            }
        }
    }

    /// The transformer's output as syntax, or a description of what in it is
    /// not syntax.
    fn heap_to_syntax(&mut self, v: Value, c: &mut Conv) -> Result<Syntax, String> {
        let span = c.span;
        if v.is_pair() {
            if let Some(orig) = c.pairs.get(&v.raw()) {
                return Ok(orig.clone());
            }
            let mut items = Vec::new();
            let mut cur = v;
            while cur.is_pair() {
                let head = self.rt.heap.car(cur);
                items.push(self.heap_to_syntax(head, c)?);
                cur = self.rt.heap.cdr(cur);
            }
            let tail = if cur == Value::NULL { None } else { Some(Box::new(self.heap_to_syntax(cur, c)?)) };
            return Ok(Syntax::new(span, Datum::List { items, tail }));
        }
        if v == Value::NULL {
            return Ok(Syntax::new(span, Datum::Nil));
        }
        if v.is_char() {
            return Ok(Syntax::new(span, Datum::Char(v.as_char())));
        }
        if v == Value::TRUE || v == Value::FALSE {
            return Ok(Syntax::new(span, Datum::Bool(v == Value::TRUE)));
        }
        if fixpt_runtime::N::load(&self.rt.heap, v).is_some() {
            let text = fixpt_runtime::write_value(&self.rt.heap, v);
            return fixpt_read::reader::parse_number(&text, 10, None)
                .map(|n| Syntax::new(span, Datum::Number(n)))
                .ok_or(text);
        }
        match self.rt.heap.obj_type(v) {
            Some(ObjType::Symbol) => {
                let id = self.identifier(c, v);
                Ok(Syntax::symbol(span, id))
            }
            Some(ObjType::String) => Ok(Syntax::new(span, Datum::Str(self.rt.heap.string_to_rust(v)))),
            Some(ObjType::Bytevector) => Ok(Syntax::new(span, Datum::Bytevector(self.rt.heap.bytevector_to_vec(v)))),
            Some(ObjType::Vector) => {
                let n = self.rt.heap.obj_len(v);
                let mut items = Vec::with_capacity(n);
                for i in 0..n {
                    let x = self.rt.heap.obj_ref(v, i);
                    items.push(self.heap_to_syntax(x, c)?);
                }
                Ok(Syntax::new(span, Datum::Vector(items)))
            }
            _ => Err(fixpt_runtime::write_value(&self.rt.heap, v)),
        }
    }
}
