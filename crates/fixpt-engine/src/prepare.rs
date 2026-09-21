//! Getting a program ready to run.
//!
//! With the Core IR in the heap this is almost nothing: lower the analysed
//! [`Program`] into a `Code` object, wrap it in a closure, and keep a root to
//! it. There is no addressing side table any more — lexical addresses are baked
//! into the lowered nodes — and no constant pool to remember to trace, since
//! constants sit inline in the node vector.
//!
//! That is the point of the whole arrangement: after this runs, *nothing the
//! engine executes lives in Rust*, so the heap can be dumped and resumed.

use crate::compile::{CompileError, compile};
use fixpt_core::ir::Program;
use fixpt_core::lower::lower;
use fixpt_heap::{Heap, ObjType, Value};
use fixpt_read::Interner;

/// Which engine the prepared code is for.
///
/// The choice is made here rather than at run time because it decides what the
/// `Code` object's body *is* — a node vector or an instruction stream — and the
/// engine that runs it has to match. A heap therefore holds code for one engine
/// or the other, which is also why each engine compiles its own prelude.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Backend {
    /// Walk the Core IR directly.
    Ast,
    /// Compile to bytecode first.
    Bytecode,
}

pub struct Prepared {
    backend: Backend,
    /// Heap root of the top-level thunk: a closure over the lowered code.
    /// `None` for a heap resumed from an image, which has no pending
    /// top-level form — only procedures to call.
    thunk_root: Option<usize>,
    /// Cached global slot of the prelude's `raise`.
    raise_slot: Option<usize>,
}

impl Prepared {
    pub fn new(heap: &mut Heap, interner: &Interner, program: &Program) -> Prepared {
        Prepared::for_backend(Backend::Ast, heap, interner, program)
            .expect("the AST backend cannot fail to prepare")
    }

    pub fn for_backend(
        backend: Backend,
        heap: &mut Heap,
        interner: &Interner,
        program: &Program,
    ) -> Result<Prepared, CompileError> {
        let thunk = build_thunk(backend, heap, interner, program)?;
        let thunk_root = heap.push_root(thunk);
        Ok(Prepared {
            backend,
            thunk_root: Some(thunk_root),
            raise_slot: None,
        })
    }

    pub fn backend(&self) -> Backend {
        self.backend
    }

    /// Re-lower after more forms have been expanded.
    ///
    /// Earlier closures are unaffected: they hold their own `Code` objects,
    /// which are heap objects in their own right and do not refer back here.
    pub fn update(
        &mut self,
        heap: &mut Heap,
        interner: &Interner,
        program: &Program,
    ) -> Result<(), CompileError> {
        let thunk = build_thunk(self.backend, heap, interner, program)?;
        match self.thunk_root {
            Some(r) => heap.set_root_at(r, thunk),
            None => self.thunk_root = Some(heap.push_root(thunk)),
        }
        Ok(())
    }

    /// A `Prepared` for a heap loaded from an image: there is no pending
    /// top-level form, but its procedures can be called.
    pub fn resumed() -> Prepared {
        Prepared::resumed_with(Backend::Ast)
    }

    pub fn resumed_with(backend: Backend) -> Prepared {
        Prepared {
            backend,
            thunk_root: None,
            raise_slot: None,
        }
    }

    pub fn thunk(&self, heap: &Heap) -> Value {
        let root = self.thunk_root.expect("no program has been prepared");
        heap.root_at(root)
    }

    /// The prelude's `raise`, if it has been defined yet. Looked up lazily,
    /// because the prelude itself is a program that runs before it exists.
    pub fn raise_procedure(&mut self, heap: &mut Heap) -> Option<Value> {
        let slot = match self.raise_slot {
            Some(s) => s,
            None => {
                let sym = heap.intern("raise");
                let s = heap.symbol_global_slot(sym);
                self.raise_slot = Some(s);
                s
            }
        };
        let v = heap.global(slot);
        if v.is_unbound() { None } else { Some(v) }
    }
}

/// The lowered program, as a closure of no arguments over the empty
/// environment.
fn build_thunk(
    backend: Backend,
    heap: &mut Heap,
    interner: &Interner,
    program: &Program,
) -> Result<Value, CompileError> {
    match backend {
        Backend::Ast => {
            let code = lower(heap, interner, program);
            // `[code, env]`: the AST engine's closures carry an environment
            // chain, and the top level's is empty.
            let closure = heap.alloc(ObjType::Closure, 2, Value::FALSE);
            heap.obj_set(closure, 0, code);
            heap.obj_set(closure, 1, Value::FALSE);
            Ok(closure)
        }
        Backend::Bytecode => {
            let code = compile(heap, interner, program)?;
            // `[code, captures…]`, and a thunk captures nothing.
            let closure = heap.alloc(ObjType::Closure, 1, Value::FALSE);
            heap.obj_set(closure, 0, code);
            Ok(closure)
        }
    }
}
