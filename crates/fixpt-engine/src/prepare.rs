//! Turning an expanded [`Program`] into something an engine can run.
//!
//! Two things happen here. Lexical addressing (see [`crate::resolve`]) is
//! computed, and one `Code` object per lambda is allocated in the heap. The
//! `Code` objects are rooted permanently, because closures point at them and
//! the printer reads a procedure's name out of them.

use crate::resolve::{resolve, Addressing};
use fixpt_core::ir::{GlobalId, LambdaId, Node, NodeId, Program};
use fixpt_heap::{ObjType, Value};
use fixpt_runtime::Runtime;

pub struct Prepared {
    pub program: Program,
    pub addressing: Addressing,
    /// Heap root index of a vector of `Code` objects, indexed by `LambdaId`.
    codes_root: usize,
    /// Cached global slot of the prelude's `raise`.
    raise_slot: Option<usize>,
}

impl Prepared {
    pub fn new(rt: &mut Runtime, program: Program) -> Prepared {
        let codes = rt.heap.make_vector(0, Value::FALSE);
        let codes_root = rt.heap.push_root(codes);
        let mut p = Prepared {
            program: Program::empty(),
            addressing: Addressing::empty(),
            codes_root,
            raise_slot: None,
        };
        p.update(rt, program);
        p
    }

    /// Re-derive the addressing and code objects after more forms have been
    /// expanded into the same arena.
    pub fn update(&mut self, rt: &mut Runtime, program: Program) {
        self.program = program;
        self.addressing = resolve(&self.program);
        let n = self.program.lambdas.len();
        let codes = rt.heap.make_vector(n, Value::FALSE);
        let old = rt.heap.root_at(self.codes_root);
        // Reuse the code objects already handed out, so closures made by
        // earlier inputs keep pointing at the same `Code`.
        let reuse = if rt.heap.is_a(old, ObjType::Vector) { rt.heap.obj_len(old) } else { 0 };
        for i in 0..reuse.min(n) {
            let c = rt.heap.obj_ref(old, i);
            rt.heap.obj_set(codes, i, c);
        }
        rt.heap.set_root_at(self.codes_root, codes);
        let p = self;
        for i in reuse..n {
            let id = LambdaId(i as u32);
            let info = p.program.lambda(id);
            let name = match info.name {
                Some(s) => {
                    let text = rt.interner.name(s).to_string();
                    rt.heap.intern(&text)
                }
                None => Value::FALSE,
            };
            let arity = info.params.len() as i64;
            let has_rest = info.rest.is_some();
            // `[name, arity, has-rest?, detail]`. For this engine `detail` is
            // the lambda index; the bytecode compiler puts a code object there
            // instead, so closures have one shape across both engines.
            let code = rt.heap.alloc(ObjType::Code, 4, Value::FALSE);
            rt.heap.obj_set(code, 0, name);
            rt.heap.obj_set(code, 1, Value::fixnum(arity));
            rt.heap.obj_set(code, 2, Value::boolean(has_rest));
            rt.heap.obj_set(code, 3, Value::fixnum(i as i64));
            let vec = rt.heap.root_at(p.codes_root);
            rt.heap.obj_set(vec, i, code);
        }
    }

    pub fn code_for(&self, rt: &Runtime, l: LambdaId) -> Value {
        let codes = rt.heap.root_at(self.codes_root);
        rt.heap.obj_ref(codes, l.index())
    }

    /// The prelude's `raise`, if it has been defined yet. Looked up lazily,
    /// because the prelude itself is a program that runs before it exists.
    pub fn raise_procedure(&mut self, rt: &mut Runtime) -> Option<Value> {
        let slot = match self.raise_slot {
            Some(s) => s,
            None => {
                let sym = rt.heap.intern("raise");
                let s = rt.heap.symbol_global_slot(sym);
                self.raise_slot = Some(s);
                s
            }
        };
        let v = rt.heap.global(slot);
        if v.is_unbound() { None } else { Some(v) }
    }

    pub fn global_name(&self, rt: &Runtime, g: GlobalId) -> String {
        // The global array is indexed by slot, and every slot belongs to a
        // symbol, so a reverse scan of the symbol table names it.
        for i in 0..rt.heap.symbol_count() {
            let sym = rt.heap.symbols_slice()[i];
            if rt.heap.symbol_global_slot(sym) == g.index() {
                return rt.heap.symbol_name(sym);
            }
        }
        format!("#<global {}>", g.0)
    }

    pub fn var_name(&self, rt: &Runtime, node: NodeId) -> String {
        match self.program.node(node) {
            Node::Ref(v) | Node::Set(v, _) => {
                rt.interner.name(self.program.var(*v).name).to_string()
            }
            _ => "a variable".into(),
        }
    }
}
