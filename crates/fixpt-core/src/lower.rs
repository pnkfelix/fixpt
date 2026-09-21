//! Lowering the Core IR into the heap.
//!
//! The Rust-side [`Program`] is a *compiler* representation: an arena, with
//! side tables the analysis passes fill in. What the engines execute is this —
//! the same program, encoded as ordinary heap objects.
//!
//! # Why it lives in the heap
//!
//! So that a dumped heap is self-contained. Larceny's interpreter survives a
//! heap dump because it is written in Scheme, which makes the structures it
//! interprets ordinary heap objects; an interpreter written in Rust over a Rust
//! arena would leave every closure pointing at something the image does not
//! contain. Putting the IR in the heap gets the same property by the same
//! means: a closure is `[code, env]`, `code` is a heap object, and everything
//! it refers to is reachable from it.
//!
//! # Encoding
//!
//! A `Code` object carries **one flat `Vector` of words** holding all of its
//! own nodes, and a node reference is a fixnum index into that vector. Not one
//! heap object per node: a flat vector is denser, is traced in one pass, and is
//! already most of the way to the bytecode the compiler will emit — so the two
//! engines end up sharing a code-object shape rather than reconciling two.
//!
//! Constants, symbols and nested `Code` objects sit inline as real `Value`s and
//! are traced automatically. Everything else is a fixnum, so the collector
//! walks the vector without needing to know the encoding at all.
//!
//! ```text
//! Const      [CONST, value]
//! Local      [LOCAL, depth, index, name]
//! Global     [GLOBAL, slot, name]
//! SetLocal   [SET_LOCAL, depth, index, name, expr]
//! SetGlobal  [SET_GLOBAL, slot, name, expr]
//! If         [IF, test, then, else]
//! Seq        [SEQ, n, e₀ … eₙ₋₁]
//! Let        [LET, n, body, init₀ … initₙ₋₁]
//! Fix        [FIX, n, body, init₀ … initₙ₋₁]
//! Lambda     [LAMBDA, code]
//! App        [APP, n, rator, rand₀ … randₙ₋₁]
//! ```
//!
//! Lexical addressing is baked into `Local`, which is what lets the separate
//! `Addressing` side table go away — it was Rust-side state that could not have
//! been dumped.
//!
//! Per-node source spans are deliberately *not* carried. Expansion-time errors
//! still have full spans, because the expander works on `Syntax` and runs
//! before lowering; what a run-time error needs is the procedure's name, and
//! that is on the `Code` object. Spans for every node would bloat every image
//! to pay for a message that is rarely better.

use crate::ir::{LambdaId, Node, NodeId, Program, VarId};
use fixpt_heap::{Heap, ObjType, Value};
use fixpt_read::Interner;

// Node tags.
pub const TAG_CONST: i64 = 0;
pub const TAG_LOCAL: i64 = 1;
pub const TAG_GLOBAL: i64 = 2;
pub const TAG_SET_LOCAL: i64 = 3;
pub const TAG_SET_GLOBAL: i64 = 4;
pub const TAG_IF: i64 = 5;
pub const TAG_SEQ: i64 = 6;
pub const TAG_LET: i64 = 7;
pub const TAG_FIX: i64 = 8;
pub const TAG_LAMBDA: i64 = 9;
pub const TAG_APP: i64 = 10;

/// `Code` payload layout.
pub const CODE_NAME: usize = 0;
pub const CODE_ARITY: usize = 1;
pub const CODE_HAS_REST: usize = 2;
/// The flat node vector.
pub const CODE_NODES: usize = 3;
/// Index of the body's root node within `CODE_NODES`.
pub const CODE_ENTRY: usize = 4;
pub const CODE_FIELDS: usize = 5;

/// Lower a whole program, returning its top-level `Code` object.
///
/// The result is a thunk of no arguments: applying it runs the program.
pub fn lower(heap: &mut Heap, interner: &Interner, program: &Program) -> Value {
    let mut l = Lowerer { heap, interner, program, scopes: Vec::new() };
    l.code_for(None, &[], None, program.body)
}

struct Lowerer<'a> {
    heap: &'a mut Heap,
    interner: &'a Interner,
    program: &'a Program,
    scopes: Vec<Vec<VarId>>,
}

impl Lowerer<'_> {
    /// Build one `Code` object: a scope for its parameters, then its body.
    fn code_for(
        &mut self,
        name: Option<fixpt_read::Sym>,
        params: &[VarId],
        rest: Option<VarId>,
        body: NodeId,
    ) -> Value {
        let mut scope = params.to_vec();
        if let Some(r) = rest {
            scope.push(r);
        }
        self.scopes.push(scope);
        let mut words: Vec<Value> = Vec::new();
        let entry = self.emit(&mut words, body);
        self.scopes.pop();

        let nodes = self.heap.vector_from(&words);
        let name_value = match name {
            Some(s) => {
                let text = self.interner.name(s).to_string();
                self.heap.intern(&text)
            }
            None => Value::FALSE,
        };
        let code = self.heap.alloc(ObjType::Code, CODE_FIELDS, Value::FALSE);
        self.heap.obj_set(code, CODE_NAME, name_value);
        self.heap.obj_set(code, CODE_ARITY, Value::fixnum(params.len() as i64));
        self.heap.obj_set(code, CODE_HAS_REST, Value::boolean(rest.is_some()));
        self.heap.obj_set(code, CODE_NODES, nodes);
        self.heap.obj_set(code, CODE_ENTRY, Value::fixnum(entry as i64));
        code
    }

    /// `(depth, index)` of a variable in the scope chain that will exist here.
    fn address(&self, v: VarId) -> (i64, i64) {
        for (back, scope) in self.scopes.iter().rev().enumerate() {
            if let Some(i) = scope.iter().position(|x| *x == v) {
                return (back as i64, i as i64);
            }
        }
        // Only reachable from a malformed program; a panic here names the
        // variable rather than silently producing a wrong address.
        panic!("unbound local {:?} during lowering", self.program.var(v).name)
    }

    fn name_of(&mut self, v: VarId) -> Value {
        let text = self.interner.name(self.program.var(v).name).to_string();
        self.heap.intern(&text)
    }

    /// Emit `node` and everything it needs, returning its offset.
    ///
    /// Children are emitted first, so a node's operands are always already
    /// placed when it is written.
    fn emit(&mut self, words: &mut Vec<Value>, node: NodeId) -> usize {
        match self.program.node(node).clone() {
            Node::Const(c) => {
                let v = self.program.constant(c);
                let at = words.len();
                words.push(Value::fixnum(TAG_CONST));
                words.push(v);
                at
            }
            Node::Ref(v) => {
                let (depth, index) = self.address(v);
                let name = self.name_of(v);
                let at = words.len();
                words.push(Value::fixnum(TAG_LOCAL));
                words.push(Value::fixnum(depth));
                words.push(Value::fixnum(index));
                words.push(name);
                at
            }
            Node::GlobalRef(g) => {
                let name = self.global_name(g);
                let at = words.len();
                words.push(Value::fixnum(TAG_GLOBAL));
                words.push(Value::fixnum(g.0 as i64));
                words.push(name);
                at
            }
            Node::Set(v, e) => {
                let expr = self.emit(words, e);
                let (depth, index) = self.address(v);
                let name = self.name_of(v);
                let at = words.len();
                words.push(Value::fixnum(TAG_SET_LOCAL));
                words.push(Value::fixnum(depth));
                words.push(Value::fixnum(index));
                words.push(name);
                words.push(Value::fixnum(expr as i64));
                at
            }
            Node::GlobalSet(g, e) => {
                let expr = self.emit(words, e);
                let name = self.global_name(g);
                let at = words.len();
                words.push(Value::fixnum(TAG_SET_GLOBAL));
                words.push(Value::fixnum(g.0 as i64));
                words.push(name);
                words.push(Value::fixnum(expr as i64));
                at
            }
            Node::If(a, b, c) => {
                let test = self.emit(words, a);
                let then = self.emit(words, b);
                let els = self.emit(words, c);
                let at = words.len();
                words.push(Value::fixnum(TAG_IF));
                words.push(Value::fixnum(test as i64));
                words.push(Value::fixnum(then as i64));
                words.push(Value::fixnum(els as i64));
                at
            }
            Node::Seq(items) => {
                let offsets: Vec<usize> =
                    items.iter().map(|n| self.emit(words, *n)).collect();
                let at = words.len();
                words.push(Value::fixnum(TAG_SEQ));
                words.push(Value::fixnum(offsets.len() as i64));
                for o in offsets {
                    words.push(Value::fixnum(o as i64));
                }
                at
            }
            Node::Let { vars, inits, body } => {
                // Initialisers are outside the new scope.
                let init_offsets: Vec<usize> =
                    inits.iter().map(|n| self.emit(words, *n)).collect();
                self.scopes.push(vars.to_vec());
                let body_offset = self.emit(words, body);
                self.scopes.pop();
                let at = words.len();
                words.push(Value::fixnum(TAG_LET));
                words.push(Value::fixnum(vars.len() as i64));
                words.push(Value::fixnum(body_offset as i64));
                for o in init_offsets {
                    words.push(Value::fixnum(o as i64));
                }
                at
            }
            Node::Fix { vars, inits, body } => {
                // …but in `letrec*` they are inside it.
                self.scopes.push(vars.to_vec());
                let init_offsets: Vec<usize> =
                    inits.iter().map(|n| self.emit(words, *n)).collect();
                let body_offset = self.emit(words, body);
                self.scopes.pop();
                let at = words.len();
                words.push(Value::fixnum(TAG_FIX));
                words.push(Value::fixnum(vars.len() as i64));
                words.push(Value::fixnum(body_offset as i64));
                for o in init_offsets {
                    words.push(Value::fixnum(o as i64));
                }
                at
            }
            Node::Lambda(l) => {
                let code = self.lambda_code(l);
                let at = words.len();
                words.push(Value::fixnum(TAG_LAMBDA));
                words.push(code);
                at
            }
            Node::App { rator, rands } => {
                let rator_offset = self.emit(words, rator);
                let rand_offsets: Vec<usize> =
                    rands.iter().map(|n| self.emit(words, *n)).collect();
                let at = words.len();
                words.push(Value::fixnum(TAG_APP));
                words.push(Value::fixnum(rand_offsets.len() as i64));
                words.push(Value::fixnum(rator_offset as i64));
                for o in rand_offsets {
                    words.push(Value::fixnum(o as i64));
                }
                at
            }
            Node::PrimCall { .. } => {
                panic!("PrimCall is produced by a pass the AST engine does not run")
            }
        }
    }

    fn lambda_code(&mut self, l: LambdaId) -> Value {
        let info = self.program.lambda(l).clone();
        self.code_for(info.name, &info.params, info.rest, info.body)
    }

    /// A global's printable name, for the "unbound variable" message.
    fn global_name(&mut self, g: crate::ir::GlobalId) -> Value {
        for i in 0..self.heap.symbol_count() {
            let sym = self.heap.symbols_slice()[i];
            if self.heap.symbol_global_slot(sym) == g.index() {
                return sym;
            }
        }
        Value::FALSE
    }
}
