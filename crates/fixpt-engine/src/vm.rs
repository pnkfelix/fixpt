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
    CODE_ARITY, CODE_ENTRY, CODE_FRAME, CODE_FREE, CODE_HAS_REST, CODE_NAME,
};
use fixpt_heap::{ObjType, Value};
use fixpt_runtime::Runtime;
use fixpt_runtime::cmarks::{self, Marks};
use fixpt_runtime::error::{Outcome, Thrown};
use fixpt_runtime::prim::{self, EngineOp, PrimKind};

const REG_CLOSURE: usize = 0;
/// The current code bloblet: its instructions are its suffix, and its
/// constants are its items, so this one register is all decoding needs.
const REG_CODE: usize = 1;
const REG_SCRATCH: usize = 2;
const N_REGS: usize = 3;

/// A pending return. Holds no `Value`s — see the module docs.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum VmFrame {
    /// The value returned here is the answer.
    Halt,
    Return {
        pc: u32,
        fp: u32,
    },
    /// `call-with-values`: the producer is running; the consumer waits at stack
    /// slot `consumer`. `mode` is how `call-with-values` itself was called,
    /// which decides where the consumer's value goes: for `Next`, to `(pc, fp)`,
    /// the call site; for `Tail`, to whatever the activation at `fp` would
    /// have returned to — the consumer call is then a tail call, so a loop
    /// through `let-values` runs in constant space; for `Framed`, to the frame
    /// already beneath this one.
    Consume {
        pc: u32,
        fp: u32,
        consumer: u32,
        mode: Call,
    },
}

const TAG_HALT: u64 = 0;
const TAG_RETURN: u64 = 1;
const TAG_CONSUME: u64 = 2;
const TAG_CONSUME_TAIL: u64 = 3;
const TAG_CONSUME_FRAMED: u64 = 4;

/// Words per encoded frame.
pub const FRAME_WORDS: usize = 4;

impl VmFrame {
    fn encode(self) -> [u64; FRAME_WORDS] {
        match self {
            VmFrame::Halt => [TAG_HALT, 0, 0, 0],
            VmFrame::Return { pc, fp } => [TAG_RETURN, pc as u64, fp as u64, 0],
            VmFrame::Consume { pc, fp, consumer, mode } => {
                let tag = match mode {
                    Call::Next => TAG_CONSUME,
                    Call::Tail => TAG_CONSUME_TAIL,
                    Call::Framed => TAG_CONSUME_FRAMED,
                };
                [tag, pc as u64, fp as u64, consumer as u64]
            }
        }
    }
    /// Move the frame's stack positions from a segment based at `from` to one
    /// based at `to` — how a composable continuation is stored relative to its
    /// own bottom and reinstated wherever it is called.
    fn rebase(self, from: u32, to: u32) -> VmFrame {
        let r = |x: u32| x - from + to;
        match self {
            VmFrame::Halt => VmFrame::Halt,
            VmFrame::Return { pc, fp } => VmFrame::Return { pc, fp: r(fp) },
            VmFrame::Consume { pc, fp, consumer, mode } => VmFrame::Consume {
                pc,
                fp: r(fp),
                consumer: r(consumer),
                mode,
            },
        }
    }

    fn decode(w: [u64; FRAME_WORDS]) -> Option<VmFrame> {
        Some(match w[0] {
            TAG_HALT => VmFrame::Halt,
            TAG_RETURN => VmFrame::Return {
                pc: w[1] as u32,
                fp: w[2] as u32,
            },
            TAG_CONSUME | TAG_CONSUME_TAIL | TAG_CONSUME_FRAMED => VmFrame::Consume {
                pc: w[1] as u32,
                fp: w[2] as u32,
                consumer: w[3] as u32,
                mode: match w[0] {
                    TAG_CONSUME => Call::Next,
                    TAG_CONSUME_TAIL => Call::Tail,
                    _ => Call::Framed,
                },
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
    /// Continuation marks, prompts and winders — see [`cmarks`].
    marks: Marks,
    /// Where a `%host` request's answer goes; `Some` while paused.
    pending_host: Option<(usize, Call)>,
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
            marks: Marks::default(),
            pending_host: None,
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
        self.marks.clear();
        self.pending_host = None;
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

    /// Continue a machine paused by `%host`, with `answer` as the value of the
    /// `%host` call.
    pub fn answer_host(&mut self, rt: &mut Runtime, p: &mut Prepared, answer: Value) -> Outcome<Value> {
        let (base, call) = self.pending_host.take().expect("resume without a paused machine");
        match self.give(rt, p, base, call, answer) {
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
                let v = rt.heap.closure_ref(self.regs[REG_CLOSURE], i as usize);
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
                let m = rt.heap.bloblet_slot(code, CODE_FREE).as_fixnum() as usize;
                // Allocation never moves anything, so the captured values can
                // be read off the stack after the closure exists.
                let from = self.stack.len() - m;
                let c = rt.heap.make_closure(code, &self.stack[from..]);
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
        rt.heap.bloblet_u32(self.regs[REG_CODE], at as usize)
    }
    #[inline]
    fn konst(&self, rt: &Runtime, k: u32) -> Value {
        // A constant is one of the code bloblet's own items, a fixed
        // distance before its instructions.
        fixpt_core::lower::code_item(&rt.heap, self.regs[REG_CODE], k as usize)
    }

    /// Point the decoding registers at whatever `stack[fp]` now holds.
    fn load_code(&mut self, rt: &Runtime) {
        let closure = self.stack[self.fp as usize];
        let code = rt.heap.closure_code(closure);
        self.regs[REG_CLOSURE] = closure;
        self.regs[REG_CODE] = code;
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
                self.marks.trim(self.frames.len());
                self.stack.truncate(self.fp as usize);
                self.fp = fp;
                self.pc = pc;
                self.load_code(rt);
                self.stack.push(v);
                Ok(None)
            }
            VmFrame::Consume { pc, fp, consumer, mode } => {
                // The producer has finished: call the consumer with the values
                // it produced, as the continuation `mode` says.
                self.frames.pop();
                self.marks.trim(self.frames.len());
                let f = self.stack[consumer as usize];
                self.stack.truncate(consumer as usize);
                let call_base = self.stack.len();
                self.stack.push(f);
                self.spread_values(rt, v);
                match mode {
                    Call::Next => {
                        // To the call site, like any other call.
                        self.frames.push(VmFrame::Return { pc, fp });
                        self.apply(rt, p, call_base, Call::Framed)
                    }
                    // A tail call from the activation that called
                    // `call-with-values`, whose only remaining business was to
                    // return this value.
                    Call::Tail => {
                        self.fp = fp;
                        self.apply(rt, p, call_base, Call::Tail)
                    }
                    Call::Framed => self.apply(rt, p, call_base, Call::Framed),
                }
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
                let code = rt.heap.closure_code(f);
                let nparams = rt.heap.bloblet_slot(code, CODE_ARITY).as_fixnum() as usize;
                let has_rest = rt.heap.bloblet_slot(code, CODE_HAS_REST).is_true();
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
                let frame = rt.heap.bloblet_slot(code, CODE_FRAME).as_fixnum() as usize;
                self.stack
                    .resize(self.fp as usize + 1 + frame, Value::UNBOUND);
                self.pc = rt.heap.bloblet_slot(code, CODE_ENTRY).as_fixnum() as u32;
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
                let vals: Vec<Value> = self.stack[base + 1..].to_vec();
                // Winding is the prelude's: see the AST engine.
                if let Some(hook) = p.global(&mut rt.heap, "%continuation-apply") {
                    let list = rt.heap.list_from(&vals);
                    self.stack.truncate(base);
                    self.stack.push(hook);
                    self.stack.push(f);
                    self.stack.push(list);
                    return self.apply(rt, p, base, call);
                }
                let value = if argc == 1 { vals[0] } else { make_values(rt, &vals) };
                self.throw(rt, p, f, value, base, call)
            }
            _ => {
                self.stack.truncate(base);
                rt.fail(&format!("attempt to call a non-procedure, with {argc} argument(s)"), &[f])
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
            // `(%hole)` — report the pending work rather than computing.
            //
            // The compiled engine knows less about this than the AST one, and
            // the difference is instructive. There is no frame saying "argument
            // 2 of 3": a call is push-operator, push-arguments, `CALL n`, so
            // until the `CALL` executes the arity is only in the instruction
            // stream. What *is* known, and is the useful part, is the operand
            // stack — the operator and every argument already evaluated, as
            // values.
            EngineOp::Hole => {
                let position = self.stack[base + 1].as_fixnum() as usize;
                let total = self.stack[base + 2].as_fixnum() as usize;
                let top = p.global(&mut rt.heap, "%toplevel-tag");
                let step = p.global(&mut rt.heap, "%abort-step");
                let prompt = top.and_then(|t| self.marks.find_prompt(t));
                let floor = prompt.map_or(0, |i| self.marks.meta[i].depth as usize);
                let report = self.describe_context(rt, base, position, total, floor);
                if let (Some(tag), Some(step), Some(pi)) = (top, step, prompt) {
                    let k = self.capture_composable(rt, base, call, pi);
                    let (pos, tot) = (self.stack[base + 1], self.stack[base + 2]);
                    let hole = cmarks::make_hole(&mut rt.heap, tag, k, &report, pos, tot);
                    let vals = rt.heap.list_from(&[hole]);
                    return self.abort_to(rt, p, pi, tag, vals, step);
                }
                self.stack.truncate(base);
                let obj = rt.error_object(&report, &[]);
                Err(Thrown::fatal(obj))
            }
            // ---- marks, prompts, composable continuations ----
            EngineOp::WithMark => {
                let (key, val, thunk) = (self.stack[base + 1], self.stack[base + 2], self.stack[base + 3]);
                let (depth, height) = self.continuation_of(base, call);
                self.marks.set_mark(depth, height, key, val);
                self.call_thunk(rt, p, base, call, thunk)
            }
            EngineOp::Wind => {
                let (winder, thunk) = (self.stack[base + 1], self.stack[base + 2]);
                let (depth, height) = self.continuation_of(base, call);
                self.marks.push_winder(depth, height, winder);
                self.call_thunk(rt, p, base, call, thunk)
            }
            EngineOp::Prompt => {
                let (tag, handler, thunk) = (self.stack[base + 1], self.stack[base + 2], self.stack[base + 3]);
                let (depth, height) = self.continuation_of(base, call);
                self.marks.push_prompt(depth, height, tag, handler);
                self.call_thunk(rt, p, base, call, thunk)
            }
            EngineOp::CurrentMarks => {
                let from = self.marks.visible_from(self.stack[base + 1]);
                let v = self.marks.mark_list(&mut rt.heap, from);
                self.give(rt, p, base, call, v)
            }
            EngineOp::FirstMark => {
                let (key, default, tag) = (self.stack[base + 1], self.stack[base + 2], self.stack[base + 3]);
                let from = self.marks.visible_from(tag);
                let v = self.marks.first(from, key).unwrap_or(default);
                self.give(rt, p, base, call, v)
            }
            EngineOp::CurrentWinders => {
                let v = self.marks.winder_list(&mut rt.heap);
                self.give(rt, p, base, call, v)
            }
            EngineOp::PromptAvailable => {
                let v = Value::boolean(self.marks.find_prompt(self.stack[base + 1]).is_some());
                self.give(rt, p, base, call, v)
            }
            EngineOp::Abort => {
                let (tag, vals, step) = (self.stack[base + 1], self.stack[base + 2], self.stack[base + 3]);
                let Some(pi) = self.marks.find_prompt(tag) else {
                    self.stack.truncate(base);
                    return rt.fail("abort-current-continuation: no prompt with that tag", &[tag]);
                };
                self.abort_to(rt, p, pi, tag, vals, step)
            }
            EngineOp::CallComposable => {
                let (f, tag) = (self.stack[base + 1], self.stack[base + 2]);
                let Some(pi) = self.marks.find_prompt(tag) else {
                    self.stack.truncate(base);
                    return rt.fail("call-with-composable-continuation: no prompt with that tag", &[tag]);
                };
                let k = self.capture_composable(rt, base, call, pi);
                self.stack.truncate(base);
                self.stack.push(f);
                self.stack.push(k);
                self.apply(rt, p, base, call)
            }
            EngineOp::Host => {
                let request: Vec<Value> = self.stack[base + 1..].to_vec();
                let request = rt.heap.list_from(&request);
                self.pending_host = Some((base, call));
                Err(Thrown::suspend(request))
            }
            EngineOp::Throw => {
                let (k, vals) = (self.stack[base + 1], self.stack[base + 2]);
                if !rt.heap.is_a(k, ObjType::Continuation) {
                    self.stack.truncate(base);
                    return rt.type_error("a continuation", k);
                }
                let Some(items) = rt.heap.list_to_vec(vals) else {
                    self.stack.truncate(base);
                    return rt.type_error("a list of values", vals);
                };
                let value = make_values(rt, &items);
                self.throw(rt, p, k, value, base, call)
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
                // Where the expression's value goes depends on how this was
                // called; the frame records it (see `VmFrame::Consume`). In tail
                // position the consumer call is a tail call, as it is in the AST
                // engine, whose `Consume` frame is simply popped before the
                // consumer runs.
                self.frames.push(VmFrame::Consume {
                    pc: self.pc,
                    fp: self.fp,
                    consumer: consumer_slot,
                    mode: call,
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
        let marks = self.marks.encode(&mut rt.heap, 0, 0, 0);
        cmarks::make_continuation(&mut rt.heap, saved_stack, saved_frames, marks, false)
    }

    /// Where the continuation of an application at `base` stands, as the
    /// (depth, height) a mark records.
    ///
    /// Unlike the AST engine this depends on the call mode. A `Next` call's
    /// continuation is the frame the call is about to push, one deeper than
    /// now, and the callee's activation will start at `base`. A tail call's
    /// continuation is this activation's own — the top frame, with the stack
    /// cut back to `fp` — which is exactly why a mark set in tail position
    /// lands on the same entry as the one before it. `Framed` has its frame
    /// already.
    fn continuation_of(&self, base: usize, call: Call) -> (u32, u32) {
        let depth = self.frames.len() as u32;
        match call {
            Call::Next => (depth + 1, base as u32),
            Call::Tail => (depth, self.fp),
            Call::Framed => (depth, base as u32),
        }
    }

    /// Call `thunk` as the continuation of the application at `base`, then
    /// drop any mark whose continuation never came to exist — a `Next` call
    /// to a primitive pushes no frame.
    fn call_thunk(
        &mut self,
        rt: &mut Runtime,
        p: &mut Prepared,
        base: usize,
        call: Call,
        thunk: Value,
    ) -> Outcome<Option<Value>> {
        self.stack.truncate(base);
        self.stack.push(thunk);
        let r = self.apply(rt, p, base, call);
        self.marks.trim(self.frames.len());
        r
    }

    /// Deliver a value from an engine op, in whichever way `call` says.
    fn give(&mut self, rt: &mut Runtime, p: &mut Prepared, base: usize, call: Call, v: Value) -> Outcome<Option<Value>> {
        self.stack.truncate(base);
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

    /// Capture from the prompt at mark entry `pi` up to the continuation of the
    /// application at `base`, as a composable continuation — a segment stored
    /// relative to its own bottom.
    ///
    /// The cut follows [`capture`](Self::capture): a tail call's own activation
    /// is dead, and a `Next` call's resume point is appended as a frame so that
    /// reinstating is an ordinary return.
    fn capture_composable(&mut self, rt: &mut Runtime, base: usize, call: Call, pi: usize) -> Value {
        let m = self.marks.meta[pi];
        let (depth, height) = (m.depth as usize, m.height);
        let cut = if call == Call::Tail { self.fp as usize } else { base };
        let saved_stack = rt.heap.vector_from(&self.stack[height as usize..cut]);
        let mut frames: Vec<VmFrame> = self.frames[depth..].iter().map(|f| f.rebase(height, 0)).collect();
        if call == Call::Next {
            frames.push(VmFrame::Return { pc: self.pc, fp: self.fp }.rebase(height, 0));
        }
        let mut bytes = Vec::with_capacity(frames.len() * FRAME_WORDS * 8);
        for f in &frames {
            for w in f.encode() {
                bytes.extend_from_slice(&w.to_le_bytes());
            }
        }
        let saved_frames = rt.heap.make_bytevector(&bytes);
        let marks = self.marks.encode(&mut rt.heap, pi + 1, m.depth, m.height);
        cmarks::make_continuation(&mut rt.heap, saved_stack, saved_frames, marks, true)
    }

    /// Deliver `value` to continuation `k` from an application at `base`.
    ///
    /// A full continuation replaces the machine. A composable one is laid on
    /// top of this application's continuation — which is where `call` says —
    /// and then, like a full one, reached by an ordinary return.
    fn throw(
        &mut self,
        rt: &mut Runtime,
        p: &mut Prepared,
        k: Value,
        value: Value,
        base: usize,
        call: Call,
    ) -> Outcome<Option<Value>> {
        if !cmarks::is_composable(&rt.heap, k) {
            return self.restore_continuation(rt, p, k, value);
        }
        let at = if call == Call::Tail { self.fp } else { base as u32 };
        if call == Call::Next {
            self.frames.push(VmFrame::Return { pc: self.pc, fp: self.fp });
        }
        let depth = self.frames.len() as u32;
        self.stack.truncate(at as usize);
        let seg = rt.heap.obj_ref(k, cmarks::K_STACK);
        for i in 0..rt.heap.obj_len(seg) {
            let v = rt.heap.obj_ref(seg, i);
            self.stack.push(v);
        }
        let bytes = rt.heap.bytevector_to_vec(rt.heap.obj_ref(k, cmarks::K_FRAMES));
        for chunk in bytes.chunks_exact(FRAME_WORDS * 8) {
            let mut w = [0u64; FRAME_WORDS];
            for (i, word) in chunk.chunks_exact(8).enumerate() {
                w[i] = u64::from_le_bytes(word.try_into().expect("8 bytes"));
            }
            let f = VmFrame::decode(w).expect("frames we encoded ourselves");
            self.frames.push(f.rebase(0, at));
        }
        let (vals, meta) = (rt.heap.obj_ref(k, cmarks::K_MARK_VALS), rt.heap.obj_ref(k, cmarks::K_MARK_META));
        self.marks.append_encoded(&rt.heap, vals, meta, depth, at);
        self.fp = self.stack.len() as u32;
        self.ret(rt, p, value)
    }

    /// Cut the machine back to where mark entry `entry` was made.
    fn cut_to(&mut self, entry: usize) {
        let m = self.marks.meta[entry];
        self.frames.truncate(m.depth as usize);
        self.stack.truncate(m.height as usize);
        self.marks.truncate(entry);
        self.fp = m.height;
    }

    /// Abort to the prompt at entry `pi`; see the AST engine's `abort_to`,
    /// which this mirrors. After a cut the value belongs to the frame now on
    /// top, so the call is `Framed`.
    fn abort_to(
        &mut self,
        rt: &mut Runtime,
        p: &mut Prepared,
        pi: usize,
        tag: Value,
        vals: Value,
        step: Value,
    ) -> Outcome<Option<Value>> {
        if let Some(wi) = self.marks.innermost_winder_above(pi) {
            let after = rt.heap.cdr(self.marks.val(wi));
            self.cut_to(wi);
            let base = self.stack.len();
            self.stack.extend_from_slice(&[step, after, tag, vals, step]);
            return self.apply(rt, p, base, Call::Framed);
        }
        let handler = self.marks.val(pi);
        let Some(items) = rt.heap.list_to_vec(vals) else {
            return rt.type_error("a list of values", vals);
        };
        self.cut_to(pi);
        let base = self.stack.len();
        self.stack.push(handler);
        self.stack.extend_from_slice(&items);
        self.apply(rt, p, base, Call::Framed)
    }

    fn restore_continuation(
        &mut self,
        rt: &mut Runtime,
        p: &mut Prepared,
        k: Value,
        value: Value,
    ) -> Outcome<Option<Value>> {
        let saved_stack = rt.heap.obj_ref(k, cmarks::K_STACK);
        let saved_frames = rt.heap.obj_ref(k, cmarks::K_FRAMES);
        self.marks.clear();
        let (vals, meta) = (rt.heap.obj_ref(k, cmarks::K_MARK_VALS), rt.heap.obj_ref(k, cmarks::K_MARK_META));
        self.marks.append_encoded(&rt.heap, vals, meta, 0, 0);
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

    // ------------------------------------------------------------- the hole
    /// Describe what the machine was in the middle of doing.
    ///
    /// `position`/`total` come from the reader: the hole is argument
    /// `position` of `total`. That is the static half, and the compiled engine
    /// needs it — its frames record no such thing, and the enclosing `CALL`
    /// has not run yet. Given it, the operand stack segments exactly: the top
    /// `position` values are this call's operator and the arguments already
    /// evaluated, and anything below belongs to calls still waiting.
    fn describe_context(
        &mut self,
        rt: &mut Runtime,
        base: usize,
        position: usize,
        total: usize,
        outer_frames: usize,
    ) -> String {
        use std::fmt::Write as _;
        let code = self.regs[REG_CODE];
        let frame = if rt.heap.is_a(code, ObjType::Code) {
            rt.heap.bloblet_slot(code, CODE_FRAME).as_fixnum() as usize
        } else {
            0
        };
        let floor = (self.fp as usize + 1 + frame).min(base);
        let pending = &self.stack[floor..base];

        let mut out = String::from("evaluation reached a hole");
        if position == 0 || position > pending.len() {
            // The reader thought the hole sat in argument `position`, and the
            // machine disagrees: a call pushes its operator and arguments into
            // the *same* activation as the hole, so if they are not on this
            // operand stack there is no such call. The enclosing form looked
            // like an application and is not one — a binding clause, a `cond`
            // clause, a macro that consumed it. Saying that is more use than
            // repeating the reader's guess as though the run confirmed it.
            out.push_str(if position == 0 {
                "\n  the hole is not in argument position"
            } else {
                "\n  the enclosing form is not an application — no operator or \n                   earlier argument was evaluated for it"
            });
        } else {
            let call = &pending[pending.len() - position..];
            let _ = write!(
                out,
                "\n  the hole is argument {position} of {total} to {}",
                fixpt_runtime::write_value(&rt.heap, call[0])
            );
            for (i, v) in call[1..].iter().enumerate() {
                let _ = write!(
                    out,
                    "\n    argument {} evaluated to {}",
                    i + 1,
                    fixpt_runtime::write_value(&rt.heap, *v)
                );
            }
            let beneath = pending.len() - position;
            if beneath > 0 {
                let _ = write!(
                    out,
                    "\n  {beneath} value(s) beneath it belong to calls still waiting"
                );
            }
        }
        let name = rt.heap.bloblet_slot(code, CODE_NAME);
        if rt.heap.is_a(name, ObjType::Symbol) {
            let _ = write!(out, "\n  inside the procedure `{}`", rt.heap.symbol_name(name));
        }
        // The first `outer_frames` frames are the top level's own machinery.
        let depth = self.frames.len().saturating_sub(outer_frames.max(1));
        if depth > 0 {
            let _ = write!(out, "\n  with {depth} call(s) pending beneath it");
        }
        out
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
            .maybe_collect(&mut [&mut self.stack, &mut self.regs, &mut self.marks.vals]);
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
    let name = rt.heap.bloblet_slot(code, CODE_NAME);
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
