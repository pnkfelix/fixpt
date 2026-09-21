//! The bytecode machine — the compiled engine.
//!
//! Same contract as the AST engine in [`interp`](crate::interp), and for the
//! same reasons: proper tail calls, recursion bounded by the heap rather than
//! by Rust's stack, re-entrant `call/cc`, and a heap that can be dumped and
//! resumed because everything it executes is a heap object. What differs is
//! only how a procedure's body is represented — a flat instruction stream
//! instead of a tree of nodes — which is why the two engines share `Code`,
//! share the primitive table, and share the prelude.
//!
//! # State
//!
//! ```text
//! stack   … caller's operands │ closure │ locals │ operands …
//!                             ↑ fp
//! ```
//!
//! One activation is `stack[fp]` — the running closure, which is also where its
//! captured values live — followed by `CODE_FRAME` local slots and then the
//! operand stack. Because the closure sits *in* the frame, the collector
//! traces the running code without the VM holding a separate root for it.
//!
//! Control frames hold `(pc, fp)` and nothing else: no `Value`s, so a captured
//! continuation is still a plain word copy. A call pushes one; a tail call
//! copies the operands down over the current frame and pushes nothing, which
//! is the whole of what makes a Scheme loop run in constant space.
//!
//! # Unbound slots
//!
//! Frame slots start at [`Value::UNBOUND`], so reading a `letrec*` binding
//! before its initialiser has run is caught rather than silently reading
//! whatever the previous activation left there. The compiler re-clears them at
//! each `letrec*` so that a continuation re-entering one behaves the same.

use crate::compile::op;
use crate::prepare::Prepared;
use fixpt_core::lower::{
    CODE_ARITY, CODE_BODY, CODE_CONSTS, CODE_ENTRY, CODE_FRAME, CODE_FREE, CODE_HAS_REST, CODE_NAME,
};
use fixpt_heap::{ObjType, Value};
use fixpt_runtime::Runtime;
use fixpt_runtime::error::{Outcome, Thrown};
use fixpt_runtime::prim::{self, EngineOp, PrimKind};

const REG_CLOSURE: usize = 0;
const REG_CODE: usize = 1;
const REG_CONSTS: usize = 2;
const REG_BODY: usize = 3;
const REG_SCRATCH: usize = 4;
const N_REGS: usize = 5;

/// A pending return. Holds no `Value`s — see the module docs.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum VmFrame {
    /// The value returned here is the answer.
    Halt,
    Return {
        pc: u32,
        fp: u32,
    },
    /// `call-with-values`: the producer is running; the consumer waits at stack
    /// slot `consumer`, and `(pc, fp)` is where the whole expression's value
    /// goes once the consumer has produced it.
    Consume {
        pc: u32,
        fp: u32,
        consumer: u32,
    },
}

const TAG_HALT: u64 = 0;
const TAG_RETURN: u64 = 1;
const TAG_CONSUME: u64 = 2;

/// Words per encoded frame.
pub const FRAME_WORDS: usize = 4;

impl VmFrame {
    fn encode(self) -> [u64; FRAME_WORDS] {
        match self {
            VmFrame::Halt => [TAG_HALT, 0, 0, 0],
            VmFrame::Return { pc, fp } => [TAG_RETURN, pc as u64, fp as u64, 0],
            VmFrame::Consume { pc, fp, consumer } => {
                [TAG_CONSUME, pc as u64, fp as u64, consumer as u64]
            }
        }
    }
    fn decode(w: [u64; FRAME_WORDS]) -> Option<VmFrame> {
        Some(match w[0] {
            TAG_HALT => VmFrame::Halt,
            TAG_RETURN => VmFrame::Return {
                pc: w[1] as u32,
                fp: w[2] as u32,
            },
            TAG_CONSUME => VmFrame::Consume {
                pc: w[1] as u32,
                fp: w[2] as u32,
                consumer: w[3] as u32,
            },
            _ => return None,
        })
    }
}

/// What happens to the value the application produces.
///
/// Threading this through `apply` rather than deciding afterwards is what keeps
/// the three cases from drifting: a tail call must not push a frame, a plain
/// call must, and an application whose control frame was already pushed must
/// push neither but still return *through* it.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum Call {
    /// The value lands on this frame's operand stack; execution continues at
    /// the next instruction.
    Next,
    /// The value is this frame's value. Reuse the frame — proper tail calls.
    Tail,
    /// A control frame is already on the stack and the value belongs to it.
    /// Build a fresh frame on top rather than reusing this one.
    Framed,
}

pub struct Vm {
    stack: Vec<Value>,
    frames: Vec<VmFrame>,
    regs: Vec<Value>,
    fp: u32,
    pc: u32,
    /// Bounds a runaway program so tests fail rather than hang. `None` is
    /// unlimited.
    pub step_limit: Option<u64>,
    steps: u64,
}

impl Default for Vm {
    fn default() -> Vm {
        Vm::new()
    }
}

impl Vm {
    pub fn new() -> Vm {
        Vm {
            stack: Vec::with_capacity(256),
            frames: Vec::with_capacity(64),
            regs: vec![Value::UNSPECIFIED; N_REGS],
            fp: 0,
            pc: 0,
            step_limit: None,
            steps: 0,
        }
    }

    fn reset(&mut self) {
        self.stack.clear();
        self.frames.clear();
        self.frames.push(VmFrame::Halt);
        self.fp = 0;
        self.pc = 0;
        self.steps = 0;
        for r in self.regs.iter_mut() {
            *r = Value::UNSPECIFIED;
        }
    }

    /// Run a prepared program to completion.
    pub fn run(&mut self, rt: &mut Runtime, p: &mut Prepared) -> Outcome<Value> {
        let thunk = p.thunk(&rt.heap);
        self.call(rt, p, thunk, &[])
    }

    /// Apply a procedure from native code, running it to completion.
    pub fn call(
        &mut self,
        rt: &mut Runtime,
        p: &mut Prepared,
        f: Value,
        args: &[Value],
    ) -> Outcome<Value> {
        self.reset();
        self.stack.push(f);
        self.stack.extend_from_slice(args);
        // The outermost application is a tail call into the `Halt` frame: its
        // value is the answer, so there is nothing to return to.
        self.fp = 0;
        match self.apply(rt, p, 0, Call::Tail) {
            Ok(Some(v)) => return Ok(v),
            Ok(None) => {}
            Err(t) => {
                if let Some(v) = self.dispatch_condition(rt, p, t)? {
                    return Ok(v);
                }
            }
        }
        self.drive(rt, p)
    }

    // ------------------------------------------------------------- the loop
    fn drive(&mut self, rt: &mut Runtime, p: &mut Prepared) -> Outcome<Value> {
        loop {
            self.steps += 1;
            if let Some(limit) = self.step_limit
                && self.steps > limit
            {
                return rt.fail("evaluation step limit exceeded", &[]);
            }
            match self.step(rt, p) {
                Ok(None) => {}
                Ok(Some(v)) => return Ok(v),
                Err(t) => {
                    if let Some(v) = self.dispatch_condition(rt, p, t)? {
                        return Ok(v);
                    }
                }
            }
        }
    }

    /// One instruction. `Some(v)` means the machine halted with `v`.
    fn step(&mut self, rt: &mut Runtime, p: &mut Prepared) -> Outcome<Option<Value>> {
        let opcode = self.word(rt, self.pc);
        match opcode {
            op::CONST => {
                let k = self.word(rt, self.pc + 1);
                self.pc += 2;
                let v = self.konst(rt, k);
                self.stack.push(v);
            }
            op::LOCAL => {
                let i = self.word(rt, self.pc + 1);
                let k = self.word(rt, self.pc + 2);
                self.pc += 3;
                let v = self.stack[self.fp as usize + 1 + i as usize];
                if v.is_unbound() {
                    return self.unbound_local(rt, k);
                }
                self.stack.push(v);
            }
            op::FREE => {
                let i = self.word(rt, self.pc + 1);
                let k = self.word(rt, self.pc + 2);
                self.pc += 3;
                let v = rt.heap.obj_ref(self.regs[REG_CLOSURE], 1 + i as usize);
                if v.is_unbound() {
                    return self.unbound_local(rt, k);
                }
                self.stack.push(v);
            }
            op::GLOBAL => {
                let g = self.word(rt, self.pc + 1);
                let k = self.word(rt, self.pc + 2);
                self.pc += 3;
                let v = rt.heap.global(g as usize);
                if v.is_unbound() {
                    let name = self.konst(rt, k);
                    let text = if rt.heap.is_a(name, ObjType::Symbol) {
                        rt.heap.symbol_name(name)
                    } else {
                        format!("#<global {g}>")
                    };
                    return rt.fail(&format!("unbound variable: {text}"), &[]);
                }
                self.stack.push(v);
            }
            op::STORE => {
                let i = self.word(rt, self.pc + 1);
                self.pc += 2;
                let v = self.stack.pop().expect("store has a value");
                self.stack[self.fp as usize + 1 + i as usize] = v;
            }
            op::SET_LOCAL => {
                let i = self.word(rt, self.pc + 1);
                self.pc += 2;
                let v = self.stack.pop().expect("set! has a value");
                self.stack[self.fp as usize + 1 + i as usize] = v;
                self.stack.push(Value::UNSPECIFIED);
            }
            op::SET_GLOBAL => {
                let g = self.word(rt, self.pc + 1);
                self.pc += 2;
                let v = self.stack.pop().expect("set! has a value");
                rt.heap.set_global(g as usize, v);
                self.stack.push(Value::UNSPECIFIED);
            }
            op::CLEAR => {
                let i = self.word(rt, self.pc + 1);
                let n = self.word(rt, self.pc + 2);
                self.pc += 3;
                let base = self.fp as usize + 1 + i as usize;
                for slot in base..base + n as usize {
                    self.stack[slot] = Value::UNBOUND;
                }
            }
            op::MAKE_BOX => {
                self.pc += 1;
                let v = *self.stack.last().expect("make-box has a value");
                let b = rt.heap.alloc(ObjType::Box, 1, v);
                *self.stack.last_mut().expect("just checked") = b;
            }
            op::BOX_REF => {
                let k = self.word(rt, self.pc + 1);
                self.pc += 2;
                let b = *self.stack.last().expect("box-ref has a box");
                let v = rt.heap.obj_ref(b, 0);
                if v.is_unbound() {
                    self.stack.pop();
                    return self.unbound_local(rt, k);
                }
                *self.stack.last_mut().expect("just checked") = v;
            }
            op::BOX_SET => {
                self.pc += 1;
                let v = self.stack.pop().expect("box-set! has a value");
                let b = self.stack.pop().expect("box-set! has a box");
                rt.heap.obj_set(b, 0, v);
                self.stack.push(Value::UNSPECIFIED);
            }
            op::CLOSURE => {
                let k = self.word(rt, self.pc + 1);
                self.pc += 2;
                let code = self.konst(rt, k);
                let m = rt.heap.obj_ref(code, CODE_FREE).as_fixnum() as usize;
                // Allocation never moves anything, so the captured values can
                // be read off the stack after the closure exists.
                let c = rt.heap.alloc(ObjType::Closure, 1 + m, Value::UNSPECIFIED);
                rt.heap.obj_set(c, 0, code);
                let from = self.stack.len() - m;
                for i in 0..m {
                    let v = self.stack[from + i];
                    rt.heap.obj_set(c, 1 + i, v);
                }
                self.stack.truncate(from);
                self.stack.push(c);
            }
            op::JUMP => {
                self.pc = self.word(rt, self.pc + 1);
            }
            op::JUMP_FALSE => {
                let t = self.word(rt, self.pc + 1);
                self.pc += 2;
                let v = self.stack.pop().expect("a test has a value");
                if v.is_false() {
                    self.pc = t;
                }
            }
            op::POP => {
                self.pc += 1;
                self.stack.pop();
            }
            op::PRIM => {
                let n = self.word(rt, self.pc + 1) as usize;
                let index = self.word(rt, self.pc + 2) as u16;
                self.pc += 3;
                let base = self.stack.len() - n;
                let def = prim::def(index);
                let PrimKind::Simple(func) = def.kind else {
                    return rt.fail(
                        &format!("{} cannot be a direct primitive call", def.name),
                        &[],
                    );
                };
                let result = func(rt, &mut self.stack[base..]);
                self.stack.truncate(base);
                self.stack.push(result?);
            }
            op::CALL | op::TAIL_CALL => {
                let n = self.word(rt, self.pc + 1) as usize;
                self.pc += 2;
                let base = self.stack.len() - n - 1;
                let mode = if opcode == op::TAIL_CALL {
                    Call::Tail
                } else {
                    Call::Next
                };
                return self.apply(rt, p, base, mode);
            }
            op::RETURN => {
                let v = self.stack.pop().expect("a body has a value");
                return self.ret(rt, p, v);
            }
            other => return rt.fail(&format!("unknown opcode {other}"), &[]),
        }
        Ok(None)
    }

    // ---------------------------------------------------------------- decode
    #[inline]
    fn word(&self, rt: &Runtime, at: u32) -> u32 {
        rt.heap.bytevector_u32(self.regs[REG_BODY], at as usize)
    }
    #[inline]
    fn konst(&self, rt: &Runtime, k: u32) -> Value {
        rt.heap.obj_ref(self.regs[REG_CONSTS], k as usize)
    }

    /// Point the decoding registers at whatever `stack[fp]` now holds.
    fn load_code(&mut self, rt: &Runtime) {
        let closure = self.stack[self.fp as usize];
        let code = rt.heap.obj_ref(closure, 0);
        self.regs[REG_CLOSURE] = closure;
        self.regs[REG_CODE] = code;
        self.regs[REG_CONSTS] = rt.heap.obj_ref(code, CODE_CONSTS);
        self.regs[REG_BODY] = rt.heap.obj_ref(code, CODE_BODY);
    }

    fn unbound_local(&mut self, rt: &mut Runtime, k: u32) -> Outcome<Option<Value>> {
        let name = self.konst(rt, k);
        let text = if rt.heap.is_a(name, ObjType::Symbol) {
            rt.heap.symbol_name(name)
        } else {
            "a variable".to_string()
        };
        rt.fail(&format!("{text} is used before it is defined"), &[])
    }

    // ---------------------------------------------------------------- return
    fn ret(&mut self, rt: &mut Runtime, p: &mut Prepared, v: Value) -> Outcome<Option<Value>> {
        let frame = *self.frames.last().expect("the Halt frame is never popped");
        match frame {
            VmFrame::Halt => Ok(Some(v)),
            VmFrame::Return { pc, fp } => {
                self.frames.pop();
                self.stack.truncate(self.fp as usize);
                self.fp = fp;
                self.pc = pc;
                self.load_code(rt);
                self.stack.push(v);
                Ok(None)
            }
            VmFrame::Consume { pc, fp, consumer } => {
                // The producer has finished. Swap its frame for the consumer's
                // and give the consumer the values it produced.
                self.frames.pop();
                let f = self.stack[consumer as usize];
                self.stack.truncate(consumer as usize);
                // Where the whole `call-with-values` expression's value goes.
                self.frames.push(VmFrame::Return { pc, fp });
                let call_base = self.stack.len();
                self.stack.push(f);
                self.spread_values(rt, v);
                self.apply(rt, p, call_base, Call::Framed)
            }
        }
    }

    /// Push the values of a `(values …)` result as separate arguments.
    fn spread_values(&mut self, rt: &mut Runtime, v: Value) {
        if rt.heap.is_a(v, ObjType::Values) {
            for i in 0..rt.heap.obj_len(v) {
                let x = rt.heap.obj_ref(v, i);
                self.stack.push(x);
            }
        } else {
            self.stack.push(v);
        }
    }

    // ----------------------------------------------------------------- apply
    /// Apply `stack[base]` to `stack[base+1..]`.
    ///
    /// Every check runs before anything is moved, so an error leaves the caller's
    /// frame — `stack[fp]` above all — exactly as it was, which is what lets a
    /// handler resume.
    fn apply(
        &mut self,
        rt: &mut Runtime,
        p: &mut Prepared,
        base: usize,
        call: Call,
    ) -> Outcome<Option<Value>> {
        self.safepoint(rt);
        let f = self.stack[base];
        let argc = self.stack.len() - base - 1;
        match rt.heap.obj_type(f) {
            Some(ObjType::Closure) => {
                let code = rt.heap.obj_ref(f, 0);
                let nparams = rt.heap.obj_ref(code, CODE_ARITY).as_fixnum() as usize;
                let has_rest = rt.heap.obj_ref(code, CODE_HAS_REST).is_true();
                if !(argc == nparams || (has_rest && argc >= nparams)) {
                    let msg = arity_message(rt, code, nparams, has_rest, argc);
                    self.stack.truncate(base);
                    return rt.fail(&msg, &[]);
                }
                if has_rest {
                    let extra: Vec<Value> = self.stack[base + 1 + nparams..].to_vec();
                    let rest = rt.heap.list_from(&extra);
                    self.stack.truncate(base + 1 + nparams);
                    self.stack.push(rest);
                }
                let nslots = nparams + usize::from(has_rest);
                match call {
                    Call::Tail => {
                        // Reuse the frame: the whole of proper tail calls.
                        let fp = self.fp as usize;
                        self.stack.copy_within(base..base + 1 + nslots, fp);
                        self.stack.truncate(fp + 1 + nslots);
                    }
                    Call::Next => {
                        self.frames.push(VmFrame::Return {
                            pc: self.pc,
                            fp: self.fp,
                        });
                        self.fp = base as u32;
                    }
                    Call::Framed => self.fp = base as u32,
                }
                let frame = rt.heap.obj_ref(code, CODE_FRAME).as_fixnum() as usize;
                self.stack
                    .resize(self.fp as usize + 1 + frame, Value::UNBOUND);
                self.pc = rt.heap.obj_ref(code, CODE_ENTRY).as_fixnum() as u32;
                self.load_code(rt);
                Ok(None)
            }
            Some(ObjType::Primitive) => {
                let index = rt.heap.obj_ref(f, 1).as_fixnum() as u16;
                let def = prim::def(index);
                if !def.accepts(argc) {
                    self.stack.truncate(base);
                    return rt.fail(&format!("{} got {argc} argument(s)", def.name), &[]);
                }
                match def.kind {
                    PrimKind::Simple(func) => {
                        let result = func(rt, &mut self.stack[base + 1..]);
                        self.stack.truncate(base);
                        let v = result?;
                        match call {
                            Call::Next => {
                                self.stack.push(v);
                                Ok(None)
                            }
                            Call::Tail => self.ret(rt, p, v),
                            Call::Framed => {
                                // The frame this returns through expects to be
                                // left at `base`.
                                self.fp = base as u32;
                                self.ret(rt, p, v)
                            }
                        }
                    }
                    PrimKind::Engine(o) => self.engine_op(rt, p, o, base, call),
                }
            }
            Some(ObjType::Continuation) => {
                let value = if argc == 1 {
                    self.stack[base + 1]
                } else {
                    let vals: Vec<Value> = self.stack[base + 1..].to_vec();
                    make_values(rt, &vals)
                };
                self.restore_continuation(rt, p, f, value)
            }
            _ => {
                self.stack.truncate(base);
                rt.fail("attempt to call a non-procedure", &[f])
            }
        }
    }

    fn engine_op(
        &mut self,
        rt: &mut Runtime,
        p: &mut Prepared,
        o: EngineOp,
        base: usize,
        call: Call,
    ) -> Outcome<Option<Value>> {
        match o {
            // (apply f a b … list)
            EngineOp::Apply => {
                let f = self.stack[base + 1];
                let last = self.stack[self.stack.len() - 1];
                let Some(tailargs) = rt.heap.list_to_vec(last) else {
                    self.stack.truncate(base);
                    return rt.type_error("a proper list as apply's last argument", last);
                };
                let middle: Vec<Value> = self.stack[base + 2..self.stack.len() - 1].to_vec();
                self.stack.truncate(base);
                self.stack.push(f);
                self.stack.extend_from_slice(&middle);
                self.stack.extend_from_slice(&tailargs);
                self.apply(rt, p, base, call)
            }
            // (%call/cc f): raw capture, with no dynamic-wind awareness. The
            // prelude wraps this to add winding.
            EngineOp::CallCC => {
                let f = self.stack[base + 1];
                let k = self.capture(rt, base, call);
                self.stack.truncate(base);
                self.stack.push(f);
                self.stack.push(k);
                self.apply(rt, p, base, call)
            }
            EngineOp::Values => {
                let vals: Vec<Value> = self.stack[base + 1..].to_vec();
                self.stack.truncate(base);
                let v = make_values(rt, &vals);
                match call {
                    Call::Next => {
                        self.stack.push(v);
                        Ok(None)
                    }
                    Call::Tail => self.ret(rt, p, v),
                    Call::Framed => {
                        self.fp = base as u32;
                        self.ret(rt, p, v)
                    }
                }
            }
            EngineOp::CallWithValues => {
                let producer = self.stack[base + 1];
                let consumer = self.stack[base + 2];
                self.stack.truncate(base);
                // Where the consumer waits while the producer runs. It has to
                // be on the stack, not in a frame: frames hold no `Value`s.
                let consumer_slot = self.stack.len() as u32;
                self.stack.push(consumer);
                let call_base = self.stack.len();
                self.stack.push(producer);
                // Where the expression's value goes. Like the AST engine, this
                // is the call site rather than the enclosing frame's own
                // continuation: neither engine makes the consumer call a tail
                // call, so both behave the same and the differential tests mean
                // something.
                self.frames.push(VmFrame::Consume {
                    pc: self.pc,
                    fp: self.fp,
                    consumer: consumer_slot,
                });
                self.apply(rt, p, call_base, Call::Framed)
            }
        }
    }

    // -------------------------------------------------------- continuations
    /// Capture the machine state below the call.
    ///
    /// For an ordinary call the current `(pc, fp)` is in no frame — it is the
    /// position the call will resume at — so it is appended as one more
    /// `Return` frame. Restoring is then an ordinary return, which is what
    /// keeps the two paths from drifting apart.
    fn capture(&mut self, rt: &mut Runtime, upto: usize, call: Call) -> Value {
        // A tail call's value is *this frame's* value, so the frame is already
        // dead: the live stack ends where it began, not at the call's operands.
        // Cutting at `upto` instead would leave the dead frame's slots between
        // the caller's operands and the value the continuation delivers.
        let cut = if call == Call::Tail {
            self.fp as usize
        } else {
            upto
        };
        let live = &self.stack[..cut];
        let saved_stack = rt.heap.vector_from(live);
        let mut frames = self.frames.clone();
        // For `Tail` and `Framed` the value belongs to the frame already on
        // top, so that frame *is* the continuation and nothing is appended.
        if call == Call::Next {
            frames.push(VmFrame::Return {
                pc: self.pc,
                fp: self.fp,
            });
        }
        let mut bytes = Vec::with_capacity(frames.len() * FRAME_WORDS * 8);
        for f in &frames {
            for w in f.encode() {
                bytes.extend_from_slice(&w.to_le_bytes());
            }
        }
        let saved_frames = rt.heap.make_bytevector(&bytes);
        let k = rt.heap.alloc(ObjType::Continuation, 2, Value::UNSPECIFIED);
        rt.heap.obj_set(k, 0, saved_stack);
        rt.heap.obj_set(k, 1, saved_frames);
        k
    }

    fn restore_continuation(
        &mut self,
        rt: &mut Runtime,
        p: &mut Prepared,
        k: Value,
        value: Value,
    ) -> Outcome<Option<Value>> {
        let saved_stack = rt.heap.obj_ref(k, 0);
        let saved_frames = rt.heap.obj_ref(k, 1);
        self.stack.clear();
        for i in 0..rt.heap.obj_len(saved_stack) {
            let v = rt.heap.obj_ref(saved_stack, i);
            self.stack.push(v);
        }
        self.frames.clear();
        let bytes = rt.heap.bytevector_to_vec(saved_frames);
        for chunk in bytes.chunks_exact(FRAME_WORDS * 8) {
            let mut w = [0u64; FRAME_WORDS];
            for (i, word) in chunk.chunks_exact(8).enumerate() {
                w[i] = u64::from_le_bytes(word.try_into().expect("8 bytes"));
            }
            self.frames
                .push(VmFrame::decode(w).expect("frames we encoded ourselves"));
        }
        // Everything above the captured stack is gone, so returning into the
        // top frame truncates nothing and lands in the right place.
        self.fp = self.stack.len() as u32;
        self.ret(rt, p, value)
    }

    // ------------------------------------------------------------ conditions
    /// A primitive raised. Hand the condition to the prelude's `raise` so user
    /// handlers get their chance; this is the only place the engine knows
    /// anything about the condition system.
    fn dispatch_condition(
        &mut self,
        rt: &mut Runtime,
        p: &mut Prepared,
        t: Thrown,
    ) -> Outcome<Option<Value>> {
        if t.fatal {
            return Err(t);
        }
        let Some(raise) = p.raise_procedure(&mut rt.heap) else {
            return Err(t);
        };
        let base = self.stack.len();
        self.stack.push(raise);
        self.stack.push(t.obj);
        match self.apply(rt, p, base, Call::Next) {
            Ok(v) => Ok(v),
            // The handler itself failed. Report the original condition rather
            // than looping through `raise` again.
            Err(_) => Err(t),
        }
    }

    // ---------------------------------------------------------- safepoint
    /// The only place a collection can happen. Every live value is in `stack`
    /// or `regs`; the decoding registers are refreshed from the frame
    /// afterwards, since the objects they name may have moved.
    fn safepoint(&mut self, rt: &mut Runtime) {
        self.regs[REG_SCRATCH] = Value::UNSPECIFIED;
        rt.heap
            .maybe_collect(&mut [&mut self.stack, &mut self.regs]);
    }
}

fn make_values(rt: &mut Runtime, vals: &[Value]) -> Value {
    if vals.len() == 1 {
        return vals[0];
    }
    let v = rt
        .heap
        .alloc(ObjType::Values, vals.len(), Value::UNSPECIFIED);
    for (i, x) in vals.iter().enumerate() {
        rt.heap.obj_set(v, i, *x);
    }
    v
}

fn arity_message(rt: &Runtime, code: Value, nparams: usize, has_rest: bool, argc: usize) -> String {
    let name = rt.heap.obj_ref(code, CODE_NAME);
    let label = if rt.heap.is_a(name, ObjType::Symbol) {
        rt.heap.symbol_name(name)
    } else {
        "procedure".to_string()
    };
    let expected = if has_rest {
        format!("at least {nparams}")
    } else {
        nparams.to_string()
    };
    format!("{label} expects {expected} argument(s), got {argc}")
}
