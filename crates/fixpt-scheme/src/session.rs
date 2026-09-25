//! A Scheme session: read, expand, run, repeat.
//!
//! One session owns one heap, one Core IR arena and one top-level scope. That
//! matters more than it looks: a closure made by an earlier input refers to its
//! lambda and its constants *by index into the arena*, so each new input has to
//! be expanded into the same arena rather than a fresh one. A REPL that started
//! a new program per line would leave every previously-defined procedure
//! pointing at nothing.

use crate::expand::{Expander, ExpanderParts};
use fixpt_core::ir::{Builder, Program};
use fixpt_engine::{Backend, Interp, Prepared, Vm};
use fixpt_heap::{ObjType, Value};
use fixpt_read::{Interner, Reader, SyntaxProfile};
use fixpt_runtime::prim::{self, PRIMITIVES};
use fixpt_runtime::{Runtime, display_value, write_value};

pub const PRELUDE: &str = include_str!("prelude.scm");

#[derive(Debug)]
pub enum SessionError {
    Read(String),
    Expand(String),
    /// A condition escaped to the top level.
    Raised(String),
    Compile(String),
    /// Evaluation reached a `,help` hole. Not a failure: the rest of the form
    /// is held, and [`Session::resume`] continues it.
    Hole(String),
}

impl std::fmt::Display for SessionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SessionError::Read(m) => write!(f, "read error: {m}"),
            SessionError::Expand(m) => write!(f, "syntax error: {m}"),
            SessionError::Raised(m) => write!(f, "error: {m}"),
            SessionError::Compile(m) => write!(f, "{m}"),
            SessionError::Hole(m) => write!(f, "{m}"),
        }
    }
}

impl std::error::Error for SessionError {}

/// The running engine. One session runs one of them: the heap holds code in
/// that engine's shape, so the choice is made when the session is created and
/// then stays put.
pub enum Engine {
    Ast(Box<Interp>),
    Bytecode(Box<Vm>),
}

impl Engine {
    /// Apply a procedure from native code, running it to completion — or to a
    /// `%host` request, which [`answer_host`](Engine::answer_host) continues.
    pub fn call(
        &mut self,
        rt: &mut Runtime,
        p: &mut Prepared,
        f: Value,
        args: &[Value],
    ) -> fixpt_runtime::Outcome<Value> {
        match self {
            Engine::Ast(i) => i.call(rt, p, f, args),
            Engine::Bytecode(v) => v.call(rt, p, f, args),
        }
    }

    pub fn answer_host(&mut self, rt: &mut Runtime, p: &mut Prepared, v: Value) -> fixpt_runtime::Outcome<Value> {
        match self {
            Engine::Ast(i) => i.answer_host(rt, p, v),
            Engine::Bytecode(vm) => vm.answer_host(rt, p, v),
        }
    }

    pub fn set_step_limit(&mut self, limit: Option<u64>) {
        match self {
            Engine::Ast(i) => i.step_limit = limit,
            Engine::Bytecode(v) => v.step_limit = limit,
        }
    }
}

pub struct Session {
    pub rt: Runtime,
    pub engine: Engine,
    /// The compiler-side arena, carried across inputs. What actually *runs* is
    /// the lowered copy in the heap; this is kept because each new input is
    /// expanded into the same arena, and because the bytecode compiler will
    /// want it too.
    program: Program,
    prepared: Prepared,
    parts: Option<ExpanderParts>,
    pub profile: SyntaxProfile,
    /// Heap root holding the most recent hole, `#f` when there is none. A
    /// root, not a Rust field, because the continuation in it must survive
    /// collections between inputs.
    hole_root: usize,
}

impl Session {
    /// A session with the primitives installed but no prelude — used to build
    /// the prelude itself, and by tests that want a bare environment.
    pub fn bare() -> Session {
        Session::bare_with(Backend::Ast)
    }

    /// A bare session for a chosen engine.
    pub fn bare_with(backend: Backend) -> Session {
        let mut rt = Runtime::new();
        install_primitives(&mut rt);
        let empty = Builder::new();
        let mut expander = Expander::new(&mut rt);
        let body = expander
            .expand_forms(&[])
            .expect("an empty program expands");
        let (program, parts) = expander.into_parts(body);
        let _ = empty;
        let prepared = Prepared::for_backend(backend, &mut rt.heap, &rt.interner, &program)
            .expect("an empty program compiles");
        let hole_root = rt.heap.push_root(Value::FALSE);
        let engine = match backend {
            Backend::Ast => Engine::Ast(Box::new(Interp::new())),
            Backend::Bytecode => Engine::Bytecode(Box::new(Vm::new())),
        };
        Session {
            rt,
            engine,
            program,
            prepared,
            parts: Some(parts),
            profile: SyntaxProfile::SCHEME,
            hole_root,
        }
    }

    pub fn new() -> Session {
        Session::with_backend(Backend::Ast)
    }

    /// A session running the bytecode engine. The prelude is compiled too:
    /// a heap holds code for one engine, so there is no mixing to get wrong.
    pub fn compiled() -> Session {
        Session::with_backend(Backend::Bytecode)
    }

    pub fn with_backend(backend: Backend) -> Session {
        let mut s = Session::bare_with(backend);
        s.eval_str("<prelude>", PRELUDE)
            .expect("the prelude must load");
        s
    }

    pub fn backend(&self) -> Backend {
        self.prepared.backend()
    }

    /// Read, expand and run `text`, returning the value of its last form.
    pub fn eval_str(&mut self, name: &str, text: &str) -> Result<Value, SessionError> {
        let forms = self.read_forms(name, text)?;
        self.eval_forms(&forms)
    }

    /// Read `text` without running it.
    ///
    /// Separate from [`eval_str`](Self::eval_str) because a caller may want to
    /// rewrite what it read — the REPL's `,help` hole does, replacing the hole
    /// with a primitive before handing the form back to be run.
    pub fn read_forms(
        &mut self,
        name: &str,
        text: &str,
    ) -> Result<Vec<fixpt_read::Syntax>, SessionError> {
        let file = self.rt.sources.add(name, text);
        let mut interner = std::mem::take(&mut self.rt.interner);
        let result = Reader::new(text, file, self.profile, &mut interner).read_all();
        self.rt.interner = interner;
        result.map_err(|e| SessionError::Read(self.describe(e.span, &e.message)))
    }

    pub fn eval_forms(&mut self, forms: &[fixpt_read::Syntax]) -> Result<Value, SessionError> {
        let parts = self
            .parts
            .take()
            .expect("expander state is always returned");
        let program = std::mem::replace(&mut self.program, Program::empty());
        let mut expander = Expander::resume(
            &mut self.rt,
            ExpanderParts {
                builder: Builder::from_program(program),
                ..parts
            },
        )
        .with_host(crate::procmacro::Host {
            engine: &mut self.engine,
            prepared: &mut self.prepared,
        });
        let expanded = expander.expand_forms(forms);
        let (program, parts) = match expanded {
            Ok(body) => expander.into_parts(body),
            Err(e) => {
                // Keep the arena even on failure: earlier definitions in the
                // same session must survive a syntax error in a later one.
                let (program, parts) = expander.into_parts(fixpt_core::ir::NodeId(0));
                self.program = program;
                self.parts = Some(parts);
                let msg = self.describe(e.span, &e.message);
                return Err(SessionError::Expand(msg));
            }
        };
        self.parts = Some(parts);
        let mut program = program;
        fixpt_core::analyze(&mut program);
        let compiled = self
            .prepared
            .update(&mut self.rt.heap, &self.rt.interner, &program);
        self.program = program;
        if let Err(e) = compiled {
            return Err(SessionError::Compile(e.to_string()));
        }
        let outcome = self.run_prepared();
        match outcome {
            Ok(v) if self.is_hole(v) => {
                self.rt.heap.set_root_at(self.hole_root, v);
                Err(SessionError::Hole(self.hole_report(v)))
            }
            Ok(v) => Ok(v),
            // `%host` paused the machine with no native caller waiting for the
            // question — it only means something inside a macro transformer.
            Err(t) if t.suspended => Err(SessionError::Raised(
                "`%host` asks the macro expander a question, and is only meaningful inside a transformer".into(),
            )),
            Err(t) => {
                let msg = self.condition_message(t.obj);
                Err(SessionError::Raised(msg))
            }
        }
    }

    /// Run the prepared program under the top level's prompts, once the
    /// prelude has defined them; the prelude itself runs bare.
    fn run_prepared(&mut self) -> fixpt_runtime::Outcome<Value> {
        let wrapper = self.prepared.global(&mut self.rt.heap, "%toplevel-run");
        match (wrapper, &mut self.engine) {
            (Some(w), Engine::Ast(i)) => {
                let thunk = self.prepared.thunk(&self.rt.heap);
                i.call(&mut self.rt, &mut self.prepared, w, &[thunk])
            }
            (Some(w), Engine::Bytecode(v)) => {
                let thunk = self.prepared.thunk(&self.rt.heap);
                v.call(&mut self.rt, &mut self.prepared, w, &[thunk])
            }
            (None, Engine::Ast(i)) => i.run(&mut self.rt, &mut self.prepared),
            (None, Engine::Bytecode(v)) => v.run(&mut self.rt, &mut self.prepared),
        }
    }

    /// A global's value, or `None` while it is unbound.
    pub fn global_value(&self, name: &str) -> Option<Value> {
        let sym = self.rt.heap.intern_existing(name)?;
        let v = self.rt.heap.global(self.rt.heap.symbol_global_slot(sym));
        if v.is_unbound() { None } else { Some(v) }
    }

    /// Apply a procedure from Rust. Unlike an input, this runs with no
    /// top-level prompt around it: it is for calling library code — the eager
    /// reader — not for running a user's program.
    pub fn call(&mut self, f: Value, args: &[Value]) -> Result<Value, SessionError> {
        match self.engine.call(&mut self.rt, &mut self.prepared, f, args) {
            Ok(v) => Ok(v),
            Err(t) => Err(SessionError::Raised(self.condition_message(t.obj))),
        }
    }

    // ------------------------------------------------------------------ holes
    /// A hole is `#(tag k report position total)` whose tag is the top level's
    /// own prompt tag — see `cmarks::make_hole`.
    fn is_hole(&mut self, v: Value) -> bool {
        let heap = &self.rt.heap;
        if !(heap.is_a(v, ObjType::Vector) && heap.obj_len(v) == 5) {
            return false;
        }
        let tag = heap.obj_ref(v, 0);
        self.prepared.global(&mut self.rt.heap, "%toplevel-tag") == Some(tag)
    }

    /// Whether a hole is held for [`resume`](Self::resume).
    pub fn has_hole(&self) -> bool {
        !self.rt.heap.root_at(self.hole_root).is_false()
    }

    /// The held hole's report, or `None` if there is none.
    pub fn held_hole_report(&mut self) -> Option<String> {
        let h = self.rt.heap.root_at(self.hole_root);
        if h.is_false() { None } else { Some(self.hole_report(h)) }
    }

    /// What the engine saw at the hole, then the marks between the hole and
    /// the top level — the part a *program* chose to expose, read from the
    /// captured continuation itself.
    fn hole_report(&mut self, hole: Value) -> String {
        let text = self.rt.heap.string_to_rust(self.rt.heap.obj_ref(hole, 2));
        let k = self.rt.heap.obj_ref(hole, 1);
        let handler_key = self.prepared.global(&mut self.rt.heap, "%handler-key");
        let marks = fixpt_runtime::cmarks::continuation_mark_list(&mut self.rt.heap, k, Value::FALSE);
        let mut lines = Vec::new();
        let mut handlers = false;
        for pair in self.rt.heap.list_to_vec(marks).unwrap_or_default() {
            let (key, val) = (self.rt.heap.car(pair), self.rt.heap.cdr(pair));
            if Some(key) == handler_key {
                // The prelude's own mark. Its value is the whole handler list,
                // innermost first, so only the innermost mark says anything.
                if !handlers && !val.is_null() {
                    let n = self.rt.heap.list_to_vec(val).map_or(0, |l| l.len());
                    lines.push(format!("{n} exception handler(s) installed around it"));
                }
                handlers = true;
                continue;
            }
            lines.push(format!(
                "marked {} = {}",
                write_value(&self.rt.heap, key),
                write_value(&self.rt.heap, val)
            ));
        }
        let mut out = text;
        for l in lines {
            out.push_str("\n  ");
            out.push_str(&l);
        }
        out
    }

    /// Continue the held hole with the value of `text`, as though the hole had
    /// evaluated to it.
    ///
    /// The value is computed first, in a fresh top-level context, and then
    /// delivered to the hole's continuation — which is composable, so it runs
    /// *on top of* this input's continuation and is delimited by this input's
    /// prompt. That is what makes a second hole reached after resuming come
    /// back here like the first. The hole is kept, so it can be resumed again
    /// with a different value; the heap, though, is shared, so whatever the
    /// first resumption mutated, the second sees.
    pub fn resume(&mut self, name: &str, text: &str) -> Result<Value, SessionError> {
        let forms = self.read_forms(name, text)?;
        self.resume_forms(&forms)
    }

    /// [`resume`](Self::resume) with the expression already read — so that a
    /// caller can rewrite it first, as the REPL does to let the value itself
    /// contain a hole.
    pub fn resume_forms(&mut self, forms: &[fixpt_read::Syntax]) -> Result<Value, SessionError> {
        let hole = self.rt.heap.root_at(self.hole_root);
        if hole.is_false() {
            return Err(SessionError::Raised("no hole to resume".into()));
        }
        let [value] = forms else {
            return Err(SessionError::Raised("`,resume` takes one expression".into()));
        };
        let k = self.rt.heap.obj_ref(hole, 1);
        let slot_sym = self.rt.heap.intern("%resuming");
        let slot = self.rt.heap.symbol_global_slot(slot_sym);
        self.rt.heap.set_global(slot, k);
        let span = value.span;
        let sym = |s: &mut Session, name: &str| fixpt_read::Syntax {
            span,
            datum: fixpt_read::Datum::Symbol(s.rt.interner.intern(name)),
        };
        let call = fixpt_read::Syntax {
            span,
            datum: fixpt_read::Datum::List {
                items: vec![sym(self, "%resume"), sym(self, "%resuming"), value.clone()],
                tail: None,
            },
        };
        self.eval_forms(&[call])
    }

    /// Evaluate and render the result the way a REPL would.
    pub fn eval_to_string(&mut self, name: &str, text: &str) -> Result<String, SessionError> {
        let v = self.eval_str(name, text)?;
        Ok(write_value(&self.rt.heap, v))
    }

    /// Run with output captured, returning `(printed, result)`.
    pub fn eval_capturing(
        &mut self,
        name: &str,
        text: &str,
    ) -> (String, Result<Value, SessionError>) {
        let saved = self.rt.capture();
        let result = self.eval_str(name, text);
        let printed = self.rt.restore(saved);
        (printed, result)
    }

    pub fn debug_node_count(&self) -> usize {
        self.program.nodes.len()
    }

    fn condition_message(&self, obj: Value) -> String {
        if self.rt.is_error_object(obj) {
            let msg = display_value(&self.rt.heap, self.rt.heap.obj_ref(obj, 1));
            let irritants = self.rt.heap.obj_ref(obj, 2);
            let list = self.rt.heap.list_to_vec(irritants).unwrap_or_default();
            if list.is_empty() {
                return msg;
            }
            let rendered: Vec<String> = list
                .iter()
                .map(|v| write_value(&self.rt.heap, *v))
                .collect();
            return format!("{msg}: {}", rendered.join(" "));
        }
        format!("uncaught: {}", write_value(&self.rt.heap, obj))
    }

    fn describe(&self, span: fixpt_read::Span, message: &str) -> String {
        format!("{}: {message}", self.rt.sources.describe(span))
    }
}

impl Default for Session {
    fn default() -> Session {
        Session::new()
    }
}

/// Give every primitive a heap object and bind it to its global slot.
pub fn install_primitives(rt: &mut Runtime) {
    for (i, def) in PRIMITIVES.iter().enumerate() {
        let name = rt.heap.intern(def.name);
        let obj = rt.heap.alloc(ObjType::Primitive, 4, Value::FALSE);
        rt.heap.obj_set(obj, 0, name);
        rt.heap.obj_set(obj, 1, Value::fixnum(i as i64));
        rt.heap.obj_set(obj, 2, Value::fixnum(def.min as i64));
        rt.heap.obj_set(
            obj,
            3,
            match def.max {
                Some(m) => Value::fixnum(m as i64),
                None => Value::FALSE,
            },
        );
        let slot = rt.heap.symbol_global_slot(name);
        rt.heap.set_global(slot, obj);
    }
    debug_assert!(prim::lookup("car").is_some());
}

/// `Default` for `Interner` so the session can take it out temporarily.
fn _assert_interner_default(_: Interner) {}
