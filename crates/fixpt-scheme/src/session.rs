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
}

impl std::fmt::Display for SessionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SessionError::Read(m) => write!(f, "read error: {m}"),
            SessionError::Expand(m) => write!(f, "syntax error: {m}"),
            SessionError::Raised(m) => write!(f, "error: {m}"),
            SessionError::Compile(m) => write!(f, "{m}"),
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
        );
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
        let outcome = match &mut self.engine {
            Engine::Ast(i) => i.run(&mut self.rt, &mut self.prepared),
            Engine::Bytecode(v) => v.run(&mut self.rt, &mut self.prepared),
        };
        match outcome {
            Ok(v) => Ok(v),
            Err(t) => {
                let msg = self.condition_message(t.obj);
                Err(SessionError::Raised(msg))
            }
        }
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
