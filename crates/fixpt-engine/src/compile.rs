//! The bytecode compiler.
//!
//! Same Core IR, same `Code` object, same heap — a different encoding of the
//! body. Where [`lower`](fixpt_core::lower) writes a tree of nodes that the AST
//! engine walks, this writes a flat instruction stream that the [`Vm`](crate::Vm)
//! executes, and the two differ in exactly the way that makes one faster than
//! the other:
//!
//! * **Variables are resolved to slots, not to a path.** The AST engine walks
//!   `depth` environment links on every reference; here a local is an index
//!   into the current frame and a captured variable an index into the closure.
//!   Both are one load.
//! * **Closures are flat.** `[code, v₀ … vₙ₋₁]` — no environment chain, so a
//!   deeply nested procedure costs no more to enter than a shallow one, and a
//!   closure keeps alive only what it actually uses.
//! * **Control is a program counter.** No frame is pushed to remember which
//!   branch of an `if` is pending; a jump suffices.
//!
//! Flat closures are what makes [`assign`](fixpt_core::assign) a prerequisite:
//! a captured variable is copied, so anything shared has to be shared through a
//! box. That pass runs here and not for the AST engine, whose environment
//! chains share by construction.
//!
//! # Encoding
//!
//! Instructions are `u32` words — one for the opcode, one per operand — held in
//! a `Bytevector` in the `Code` object's [`CODE_BODY`] slot. Words rather than
//! packed bytes because the whole point of this design is that simplicity is
//! affordable: decoding is an array index either way, and the density that a
//! byte encoding buys would cost a decoder.
//!
//! Values an instruction needs — quoted data, procedure names for error
//! messages, nested `Code` objects — live in the `Code`'s [`CODE_CONSTS`]
//! vector and are named by index, because a `Bytevector` is not traced. That
//! split is the one real constraint the collector imposes on the encoding.

use fixpt_core::assign::{self, BoxPrims};
use fixpt_core::ir::{LambdaId, Node, NodeId, Program, VarId};
use fixpt_core::lower::{
    CODE_ARITY, CODE_CONSTS, CODE_ENTRY, CODE_FIELDS, CODE_FRAME, CODE_FREE, CODE_HAS_REST,
    CODE_NAME,
};
use fixpt_heap::{Heap, ObjType, Value};
use fixpt_read::Interner;
use fixpt_runtime::prim::{self, PrimKind};
use std::collections::HashMap;

/// Opcodes. Operand counts are in the comments and encoded in [`op::len`].
pub mod op {
    /// `CONST k` — push `consts[k]`.
    pub const CONST: u32 = 0;
    /// `LOCAL i k` — push frame slot `i`; `consts[k]` names it for errors.
    pub const LOCAL: u32 = 1;
    /// `FREE i k` — push capture `i` of the running closure.
    pub const FREE: u32 = 2;
    /// `GLOBAL g k` — push global `g`.
    pub const GLOBAL: u32 = 3;
    /// `STORE i` — pop into frame slot `i`, leaving nothing.
    pub const STORE: u32 = 4;
    /// `SET_LOCAL i` — pop into frame slot `i`, push unspecified.
    pub const SET_LOCAL: u32 = 5;
    /// `SET_GLOBAL g` — pop into global `g`, push unspecified.
    pub const SET_GLOBAL: u32 = 6;
    /// `CLOSURE k` — `consts[k]` is a `Code`; capture its `CODE_FREE` values
    /// from the top of the stack.
    pub const CLOSURE: u32 = 7;
    pub const JUMP: u32 = 8;
    /// `JUMP_FALSE t` — pop; jump if false.
    pub const JUMP_FALSE: u32 = 9;
    pub const POP: u32 = 10;
    /// `CALL n` — `f a₀ … aₙ₋₁` are on top of the stack.
    pub const CALL: u32 = 11;
    /// `TAIL_CALL n` — the same, reusing the current frame.
    pub const TAIL_CALL: u32 = 12;
    pub const RETURN: u32 = 13;
    /// `PRIM n p` — apply primitive `p` to the top `n` values.
    pub const PRIM: u32 = 14;
    /// `CLEAR i n` — set frame slots `i … i+n-1` to unbound.
    pub const CLEAR: u32 = 15;
    /// `MAKE_BOX` — replace the top of the stack with a box holding it.
    pub const MAKE_BOX: u32 = 16;
    /// `BOX_REF k` — replace a box with its contents; `consts[k]` names the
    /// variable if the contents turn out to be unbound.
    pub const BOX_REF: u32 = 17;
    /// `BOX_SET` — pop a value and a box, store, push unspecified.
    pub const BOX_SET: u32 = 18;

    /// Words per instruction, opcode included.
    pub fn len(opcode: u32) -> usize {
        match opcode {
            POP | RETURN | MAKE_BOX | BOX_SET => 1,
            CONST | STORE | SET_LOCAL | SET_GLOBAL | CLOSURE | JUMP | JUMP_FALSE | CALL
            | TAIL_CALL | BOX_REF => 2,
            LOCAL | FREE | GLOBAL | PRIM | CLEAR => 3,
            _ => 1,
        }
    }

    pub fn name(opcode: u32) -> &'static str {
        match opcode {
            CONST => "const",
            LOCAL => "local",
            FREE => "free",
            GLOBAL => "global",
            STORE => "store",
            SET_LOCAL => "set-local",
            SET_GLOBAL => "set-global",
            CLOSURE => "closure",
            JUMP => "jump",
            JUMP_FALSE => "jump-false",
            POP => "pop",
            CALL => "call",
            TAIL_CALL => "tail-call",
            RETURN => "return",
            PRIM => "prim",
            CLEAR => "clear",
            MAKE_BOX => "make-box",
            BOX_REF => "box-ref",
            BOX_SET => "box-set!",
            _ => "?",
        }
    }
}

#[derive(Debug)]
pub struct CompileError(pub String);

impl std::fmt::Display for CompileError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "compile error: {}", self.0)
    }
}

impl std::error::Error for CompileError {}

/// Compile a whole program, returning its top-level `Code` object: a thunk of
/// no arguments whose application runs the program.
///
/// Assignment conversion happens here rather than in the caller, so that a
/// front end cannot forget it and get silently wrong `set!` semantics.
pub fn compile(
    heap: &mut Heap,
    interner: &Interner,
    program: &Program,
) -> Result<Value, CompileError> {
    let prims = BoxPrims {
        make: prim::lookup("%make-box").expect("%make-box is a primitive"),
        get: prim::lookup("%box-ref").expect("%box-ref is a primitive"),
        set: prim::lookup("%box-set!").expect("%box-set! is a primitive"),
    };
    let mut converted = assign::convert(program, prims);
    // Boxing rewrites the tree, so the free-variable sets — which are the
    // capture layout — have to be recomputed against what will actually run.
    fixpt_core::analyze(&mut converted);

    let mut c = Compiler {
        heap,
        interner,
        program: &converted,
        global_names: HashMap::new(),
        boxes: prims,
    };
    c.code_for(None, &[], None, converted.body)
}

struct Compiler<'a> {
    heap: &'a mut Heap,
    interner: &'a Interner,
    program: &'a Program,
    global_names: HashMap<usize, Value>,
    boxes: BoxPrims,
}

/// Where a variable lives in the code object being compiled.
#[derive(Copy, Clone)]
enum Loc {
    Local(u32),
    Free(u32),
}

/// The compile-time environment of one code object.
struct Scope {
    places: HashMap<VarId, Loc>,
    /// Next unallocated frame slot. Slots are never reused across sibling
    /// `let`s: an activation costs a few extra words and the allocator stays a
    /// counter.
    next: u32,
    frame: u32,
    code: Vec<u32>,
    consts: Vec<Value>,
}

impl Scope {
    fn alloc(&mut self, v: VarId) -> u32 {
        let slot = self.next;
        self.next += 1;
        self.frame = self.frame.max(self.next);
        self.places.insert(v, Loc::Local(slot));
        slot
    }
    fn emit(&mut self, words: &[u32]) {
        self.code.extend_from_slice(words);
    }
    /// Emit a jump with a placeholder target, returning the operand's index.
    fn jump(&mut self, opcode: u32) -> usize {
        self.code.push(opcode);
        self.code.push(0);
        self.code.len() - 1
    }
    fn patch(&mut self, at: usize) {
        self.code[at] = self.code.len() as u32;
    }
    /// Intern a constant. Identical values share a slot, which is what keeps
    /// repeated `(quote x)` of one datum `eq?`.
    fn constant(&mut self, v: Value) -> u32 {
        if let Some(i) = self.consts.iter().position(|c| *c == v) {
            return i as u32;
        }
        self.consts.push(v);
        self.consts.len() as u32 - 1
    }
}

impl Compiler<'_> {
    /// Compile one code object: parameters, then captures, then the body.
    fn code_for(
        &mut self,
        name: Option<fixpt_read::Sym>,
        params: &[VarId],
        rest: Option<VarId>,
        body: NodeId,
    ) -> Result<Value, CompileError> {
        self.code_for_lambda(name, params, rest, body, &[])
    }

    fn code_for_lambda(
        &mut self,
        name: Option<fixpt_read::Sym>,
        params: &[VarId],
        rest: Option<VarId>,
        body: NodeId,
        free: &[VarId],
    ) -> Result<Value, CompileError> {
        let mut scope = Scope {
            places: HashMap::new(),
            next: 0,
            frame: 0,
            code: Vec::new(),
            consts: Vec::new(),
        };
        for p in params {
            scope.alloc(*p);
        }
        if let Some(r) = rest {
            scope.alloc(r);
        }
        for (i, v) in free.iter().enumerate() {
            // A capture shadows nothing: alpha-renaming means no variable is
            // both a parameter here and free here.
            scope.places.insert(*v, Loc::Free(i as u32));
        }

        self.expr(&mut scope, body, true)?;
        scope.emit(&[op::RETURN]);

        let mut bytes = Vec::with_capacity(scope.code.len() * 4);
        for w in &scope.code {
            bytes.extend_from_slice(&w.to_le_bytes());
        }
        let bytecode = self.heap.make_bytevector(&bytes);
        let consts = self.heap.vector_from(&scope.consts);
        let name_value = match name {
            Some(s) => {
                let text = self.interner.name(s).to_string();
                self.heap.intern(&text)
            }
            None => Value::FALSE,
        };
        let code = self.heap.alloc(ObjType::Code, CODE_FIELDS, Value::FALSE);
        self.heap.obj_set(code, CODE_NAME, name_value);
        self.heap
            .obj_set(code, CODE_ARITY, Value::fixnum(params.len() as i64));
        self.heap
            .obj_set(code, CODE_HAS_REST, Value::boolean(rest.is_some()));
        self.heap
            .obj_set(code, fixpt_core::lower::CODE_BODY, bytecode);
        self.heap.obj_set(code, CODE_ENTRY, Value::fixnum(0));
        self.heap.obj_set(code, CODE_CONSTS, consts);
        self.heap
            .obj_set(code, CODE_FRAME, Value::fixnum(scope.frame as i64));
        self.heap
            .obj_set(code, CODE_FREE, Value::fixnum(free.len() as i64));
        Ok(code)
    }

    fn name_value(&mut self, v: VarId) -> Value {
        let text = self.interner.name(self.program.var(v).name).to_string();
        self.heap.intern(&text)
    }

    /// The symbol a global slot belongs to, for error messages. Cached: the
    /// heap's symbol table has no reverse index, and a REPL recompiles often.
    fn global_name(&mut self, slot: usize) -> Value {
        if let Some(v) = self.global_names.get(&slot) {
            return *v;
        }
        let mut found = Value::FALSE;
        for i in 0..self.heap.symbol_count() {
            let sym = self.heap.symbols_slice()[i];
            if self.heap.symbol_global_slot(sym) == slot {
                found = sym;
                break;
            }
        }
        self.global_names.insert(slot, found);
        found
    }

    /// Compile `node`, leaving its value on the stack.
    ///
    /// `tail` says whether the value becomes the enclosing procedure's result.
    /// It is threaded rather than computed afterwards because it is what turns
    /// a `CALL` into a `TAIL_CALL`, and hence what makes a Scheme loop run in
    /// constant space.
    fn expr(&mut self, s: &mut Scope, node: NodeId, tail: bool) -> Result<(), CompileError> {
        match self.program.node(node).clone() {
            Node::Const(c) => {
                let v = self.program.constant(c);
                let k = s.constant(v);
                s.emit(&[op::CONST, k]);
            }
            Node::Ref(v) => {
                let name = self.name_value(v);
                let k = s.constant(name);
                match self.place(s, v)? {
                    Loc::Local(i) => s.emit(&[op::LOCAL, i, k]),
                    Loc::Free(i) => s.emit(&[op::FREE, i, k]),
                }
            }
            Node::GlobalRef(g) => {
                let name = self.global_name(g.index());
                let k = s.constant(name);
                s.emit(&[op::GLOBAL, g.0, k]);
            }
            Node::Set(v, e) => {
                self.expr(s, e, false)?;
                match self.place(s, v)? {
                    Loc::Local(i) => s.emit(&[op::SET_LOCAL, i]),
                    Loc::Free(_) => {
                        // Assignment conversion boxes every assigned variable,
                        // so the only `Set` left is the prologue that installs
                        // a boxed parameter's cell — always into a local.
                        return Err(CompileError(
                            "assignment to a captured variable survived boxing".into(),
                        ));
                    }
                }
            }
            Node::GlobalSet(g, e) => {
                self.expr(s, e, false)?;
                s.emit(&[op::SET_GLOBAL, g.0]);
            }
            Node::If(test, then, els) => {
                self.expr(s, test, false)?;
                let to_else = s.jump(op::JUMP_FALSE);
                self.expr(s, then, tail)?;
                let past = s.jump(op::JUMP);
                s.patch(to_else);
                self.expr(s, els, tail)?;
                s.patch(past);
            }
            Node::Seq(items) => {
                let last = items.len() - 1;
                for (i, n) in items.iter().enumerate() {
                    if i == last {
                        self.expr(s, *n, tail)?;
                    } else {
                        self.expr(s, *n, false)?;
                        s.emit(&[op::POP]);
                    }
                }
            }
            Node::Let { vars, inits, body } => {
                // Initialisers are outside the bindings' scope, and slots are
                // never reused, so each one can simply be stored as it is
                // produced.
                for (v, init) in vars.iter().zip(inits.iter()) {
                    self.expr(s, *init, false)?;
                    let slot = s.alloc(*v);
                    s.emit(&[op::STORE, slot]);
                }
                self.expr(s, body, tail)?;
            }
            Node::Fix { vars, inits, body } => {
                // `letrec*`: bind first, then initialise left to right. The
                // slots start unbound so a use before initialisation is caught
                // rather than reading whatever the frame held.
                let first = s.next;
                for v in vars.iter() {
                    s.alloc(*v);
                }
                if !vars.is_empty() {
                    s.emit(&[op::CLEAR, first, vars.len() as u32]);
                }
                for (i, init) in inits.iter().enumerate() {
                    self.expr(s, *init, false)?;
                    s.emit(&[op::STORE, first + i as u32]);
                }
                self.expr(s, body, tail)?;
            }
            Node::Lambda(l) => self.closure(s, l)?,
            Node::App { rator, rands } => {
                self.expr(s, rator, false)?;
                for r in rands.iter() {
                    self.expr(s, *r, false)?;
                }
                let n = rands.len() as u32;
                s.emit(&[if tail { op::TAIL_CALL } else { op::CALL }, n]);
            }
            // Boxes get their own instructions rather than going through the
            // generic primitive call. Not only for speed — though a captured
            // variable is read on every recursive call — but because `BOX_REF`
            // carries the variable's name, so an uninitialised `letrec*`
            // binding reports what it was rather than "a variable".
            Node::PrimCall { prim: p, rands } if p == self.boxes.make && rands.len() == 1 => {
                self.expr(s, rands[0], false)?;
                s.emit(&[op::MAKE_BOX]);
            }
            Node::PrimCall { prim: p, rands } if p == self.boxes.get && rands.len() == 1 => {
                let name = match self.program.node(rands[0]) {
                    Node::Ref(v) => self.name_value(*v),
                    _ => Value::FALSE,
                };
                let k = s.constant(name);
                self.expr(s, rands[0], false)?;
                s.emit(&[op::BOX_REF, k]);
            }
            Node::PrimCall { prim: p, rands } if p == self.boxes.set && rands.len() == 2 => {
                self.expr(s, rands[0], false)?;
                self.expr(s, rands[1], false)?;
                s.emit(&[op::BOX_SET]);
            }
            Node::PrimCall { prim: p, rands } => {
                let def = prim::def(p);
                if !matches!(def.kind, PrimKind::Simple(_)) {
                    return Err(CompileError(format!(
                        "{} needs the engine and cannot be a direct primitive call",
                        def.name
                    )));
                }
                for r in rands.iter() {
                    self.expr(s, *r, false)?;
                }
                s.emit(&[op::PRIM, rands.len() as u32, p as u32]);
            }
        }
        Ok(())
    }

    /// Build a closure: push each captured value, then fold them in.
    fn closure(&mut self, s: &mut Scope, l: LambdaId) -> Result<(), CompileError> {
        let info = self.program.lambda(l).clone();
        let code =
            self.code_for_lambda(info.name, &info.params, info.rest, info.body, &info.free)?;
        // Captures are pushed in `info.free` order, which is the layout the
        // compiled body was just given.
        for v in &info.free {
            let name = self.name_value(*v);
            let k = s.constant(name);
            match self.place(s, *v)? {
                Loc::Local(i) => s.emit(&[op::LOCAL, i, k]),
                Loc::Free(i) => s.emit(&[op::FREE, i, k]),
            }
        }
        let k = s.constant(code);
        s.emit(&[op::CLOSURE, k]);
        Ok(())
    }

    fn place(&self, s: &Scope, v: VarId) -> Result<Loc, CompileError> {
        s.places.get(&v).copied().ok_or_else(|| {
            CompileError(format!(
                "{} is not in scope during compilation",
                self.interner.name(self.program.var(v).name)
            ))
        })
    }
}

/// Render a code object's instructions, one per line. For `fixpt disassemble`
/// and for making a compiler bug legible in a test failure.
pub fn disassemble(heap: &Heap, code: Value) -> String {
    use std::fmt::Write as _;
    let body = heap.obj_ref(code, fixpt_core::lower::CODE_BODY);
    if !heap.is_a(body, ObjType::Bytevector) {
        return "<interpreted code>".to_string();
    }
    let consts = heap.obj_ref(code, CODE_CONSTS);
    let bytes = heap.bytevector_to_vec(body);
    let words: Vec<u32> = bytes
        .chunks_exact(4)
        .map(|c| u32::from_le_bytes(c.try_into().expect("4 bytes")))
        .collect();
    let name = heap.obj_ref(code, CODE_NAME);
    let label = if heap.is_a(name, ObjType::Symbol) {
        heap.symbol_name(name)
    } else {
        "?".into()
    };
    let mut out = format!(
        "code {label} arity={} rest={} frame={} free={}\n",
        heap.obj_ref(code, CODE_ARITY).as_fixnum(),
        heap.obj_ref(code, CODE_HAS_REST).is_true(),
        heap.obj_ref(code, CODE_FRAME).as_fixnum(),
        heap.obj_ref(code, CODE_FREE).as_fixnum(),
    );
    let mut pc = 0usize;
    while pc < words.len() {
        let opcode = words[pc];
        let n = op::len(opcode);
        let _ = write!(out, "  {pc:4}  {:<11}", op::name(opcode));
        for w in &words[pc + 1..(pc + n).min(words.len())] {
            let _ = write!(out, " {w}");
        }
        if matches!(opcode, op::CONST | op::CLOSURE | op::BOX_REF) {
            let v = heap.obj_ref(consts, words[pc + 1] as usize);
            let _ = write!(out, "   ; {}", fixpt_runtime::write_value(heap, v));
        }
        out.push('\n');
        pc += n;
    }
    out
}
