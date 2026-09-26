//! The AST machine — the interpreted engine.
//!
//! An explicit-stack machine over the **heap-resident** Core IR. Three
//! properties follow from that, and all three are requirements rather than
//! refinements:
//!
//! * **Proper tail calls.** Applying a procedure never pushes a frame — the
//!   caller's pending work is already a frame, or there is none — so a loop
//!   written as tail recursion runs in constant space.
//! * **Unbounded recursion depth.** Scheme recursion consumes the machine's own
//!   `Vec`s, not the Rust call stack.
//! * **Re-entrant `call/cc`.** A continuation is a copy of the value stack and
//!   an encoding of the frame stack; because frames hold no heap references,
//!   that encoding is plain words.
//!
//! And one that follows from the IR living in the heap: a closure is
//! `[code, env]` where everything reachable is a heap object, so **a dumped
//! heap can be resumed by this engine** — nothing it executes lives in Rust.
//!
//! The current `Code` object is a register, and a node is an offset into that
//! code's flat node vector. Frames therefore hold offsets, never references,
//! and each frame saves the environment *and* the code so the pair can be
//! restored on resume.

use crate::frame::{FRAME_WORDS, Frame, SAVED_SLOTS};
use crate::prepare::Prepared;
use fixpt_core::lower::{
    CODE_ARITY, CODE_ENTRY, CODE_HAS_REST, CODE_NAME, TAG_APP, TAG_CONST, TAG_FIX,
    TAG_GLOBAL, TAG_IF, TAG_LAMBDA, TAG_LET, TAG_LOCAL, TAG_SEQ, TAG_SET_GLOBAL, TAG_SET_LOCAL,
};
use fixpt_heap::{ObjType, Value};
use fixpt_runtime::Runtime;
use fixpt_runtime::cmarks::{self, Marks};
use fixpt_runtime::error::{Outcome, Thrown};
use fixpt_runtime::prim::{self, EngineOp, PrimKind};

/// Register file. Kept as one slice so the root set is two contiguous ranges.
const REG_ACC: usize = 0;
const REG_ENV: usize = 1;
const REG_CODE: usize = 2;
const REG_SCRATCH: usize = 3;
const N_REGS: usize = 4;

enum Control {
    /// Evaluate the node at this offset in the current code.
    Eval(u32),
    /// `acc` holds a value; resume the top frame.
    Return,
}

pub struct Interp {
    stack: Vec<Value>,
    frames: Vec<Frame>,
    /// Continuation marks, prompts and winders, beside the frames — see
    /// [`cmarks`]. A third root slice for the collector.
    marks: Marks,
    /// Where a `%host` request's answer goes: the stack height of the
    /// application that asked. `Some` exactly while the machine is paused.
    pending_host: Option<usize>,
    regs: Vec<Value>,
    /// Bounds a runaway program so tests fail rather than hang. `None` is
    /// unlimited.
    pub step_limit: Option<u64>,
    steps: u64,
}

impl Default for Interp {
    fn default() -> Interp {
        Interp::new()
    }
}

impl Interp {
    pub fn new() -> Interp {
        Interp {
            stack: Vec::with_capacity(256),
            frames: Vec::with_capacity(64),
            marks: Marks::default(),
            pending_host: None,
            regs: vec![Value::UNSPECIFIED; N_REGS],
            step_limit: None,
            steps: 0,
        }
    }

    #[inline]
    fn acc(&self) -> Value {
        self.regs[REG_ACC]
    }
    #[inline]
    fn set_acc(&mut self, v: Value) {
        self.regs[REG_ACC] = v;
    }
    #[inline]
    fn env(&self) -> Value {
        self.regs[REG_ENV]
    }
    #[inline]
    fn set_env(&mut self, v: Value) {
        self.regs[REG_ENV] = v;
    }
    #[inline]
    fn code(&self) -> Value {
        self.regs[REG_CODE]
    }
    #[inline]
    fn set_code(&mut self, v: Value) {
        self.regs[REG_CODE] = v;
    }

    /// One word of the current code's node vector.
    #[inline]
    fn word(&self, rt: &Runtime, at: u32) -> Value {
        // A node is one of the code bloblet's own items: one load, at a
        // fixed distance before the code.
        fixpt_core::lower::code_item(&rt.heap, self.code(), at as usize)
    }
    #[inline]
    fn offset(&self, rt: &Runtime, at: u32) -> u32 {
        self.word(rt, at).as_fixnum() as u32
    }

    fn reset(&mut self) {
        self.stack.clear();
        self.frames.clear();
        self.frames.push(Frame::Halt);
        self.marks.clear();
        self.pending_host = None;
        self.set_env(Value::FALSE);
        self.set_code(Value::FALSE);
        self.set_acc(Value::UNSPECIFIED);
        self.steps = 0;
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
        let saved = self.save(rt);
        let base = saved as usize + SAVED_SLOTS;
        self.stack.push(f);
        self.stack.extend_from_slice(args);
        let control = self.apply(rt, p, base)?;
        self.drive(rt, p, control)
    }

    /// Continue a machine paused by `%host`, with `answer` as the value of the
    /// `%host` call.
    pub fn answer_host(&mut self, rt: &mut Runtime, p: &mut Prepared, answer: Value) -> Outcome<Value> {
        let at = self.pending_host.take().expect("resume without a paused machine");
        self.stack.truncate(at);
        self.set_acc(answer);
        self.drive(rt, p, Control::Return)
    }

    fn drive(&mut self, rt: &mut Runtime, p: &mut Prepared, start: Control) -> Outcome<Value> {
        let mut control = start;
        loop {
            self.steps += 1;
            if let Some(limit) = self.step_limit
                && self.steps > limit
            {
                return rt.fail("evaluation step limit exceeded", &[]);
            }
            control = match control {
                Control::Eval(node) => match self.eval(rt, p, node) {
                    Ok(c) => c,
                    Err(t) => match self.dispatch_condition(rt, p, t)? {
                        Some(c) => c,
                        None => return Err(t),
                    },
                },
                Control::Return => {
                    let frame = *self.frames.last().expect("the Halt frame is never popped");
                    if matches!(frame, Frame::Halt) {
                        return Ok(self.acc());
                    }
                    self.frames.pop();
                    // Whatever was attached to the continuation that just
                    // returned goes with it.
                    self.marks.trim(self.frames.len());
                    match self.resume(rt, p, frame) {
                        Ok(c) => c,
                        Err(t) => match self.dispatch_condition(rt, p, t)? {
                            Some(c) => c,
                            None => return Err(t),
                        },
                    }
                }
            };
        }
    }

    /// A primitive raised. Unless the condition has already been through the
    /// handler chain, hand it to the prelude's `raise`, so user handlers get
    /// their chance. This is the only place the engine knows anything about the
    /// condition system.
    fn dispatch_condition(
        &mut self,
        rt: &mut Runtime,
        p: &mut Prepared,
        t: Thrown,
    ) -> Outcome<Option<Control>> {
        if t.fatal {
            return Ok(None);
        }
        let Some(raise) = p.raise_procedure(&mut rt.heap) else {
            return Ok(None);
        };
        let saved = self.save(rt);
        let base = saved as usize + SAVED_SLOTS;
        self.stack.push(raise);
        self.stack.push(t.obj);
        Ok(Some(self.apply(rt, p, base)?))
    }

    /// Push the environment and code, returning the slot they start at.
    fn save(&mut self, _rt: &Runtime) -> u32 {
        let slot = self.stack.len() as u32;
        let e = self.env();
        let c = self.code();
        self.stack.push(e);
        self.stack.push(c);
        slot
    }

    fn restore(&mut self, saved: u32) {
        let e = self.stack[saved as usize];
        let c = self.stack[saved as usize + 1];
        self.set_env(e);
        self.set_code(c);
    }

    // ------------------------------------------------------------ evaluation
    fn eval(&mut self, rt: &mut Runtime, _p: &mut Prepared, at: u32) -> Outcome<Control> {
        let tag = self.word(rt, at).as_fixnum();
        match tag {
            TAG_CONST => {
                let v = self.word(rt, at + 1);
                self.set_acc(v);
                Ok(Control::Return)
            }
            TAG_LOCAL => {
                let depth = self.offset(rt, at + 1);
                let index = self.offset(rt, at + 2);
                let v = self.lookup(rt, depth, index);
                if v.is_unbound() {
                    let name = self.word(rt, at + 3);
                    return self.unbound_local(rt, name);
                }
                self.set_acc(v);
                Ok(Control::Return)
            }
            TAG_GLOBAL => {
                let slot = self.offset(rt, at + 1) as usize;
                let v = rt.heap.global(slot);
                if v.is_unbound() {
                    let name = self.word(rt, at + 2);
                    let text = if rt.heap.is_a(name, ObjType::Symbol) {
                        rt.heap.symbol_name(name)
                    } else {
                        format!("#<global {slot}>")
                    };
                    return rt.fail(&format!("unbound variable: {text}"), &[]);
                }
                self.set_acc(v);
                Ok(Control::Return)
            }
            TAG_SET_LOCAL => {
                let saved = self.save(rt);
                self.frames.push(Frame::AssignLocal { node: at, saved });
                Ok(Control::Eval(self.offset(rt, at + 4)))
            }
            TAG_SET_GLOBAL => {
                let slot = self.offset(rt, at + 1);
                let saved = self.save(rt);
                self.frames.push(Frame::AssignGlobal { slot, saved });
                Ok(Control::Eval(self.offset(rt, at + 3)))
            }
            TAG_IF => {
                let then = self.offset(rt, at + 2);
                let els = self.offset(rt, at + 3);
                let saved = self.save(rt);
                self.frames.push(Frame::Branch { then, els, saved });
                Ok(Control::Eval(self.offset(rt, at + 1)))
            }
            TAG_SEQ => {
                let saved = self.save(rt);
                self.frames.push(Frame::SeqNext {
                    seq: at,
                    index: 1,
                    saved,
                });
                Ok(Control::Eval(self.offset(rt, at + 2)))
            }
            TAG_LET => {
                let n = self.offset(rt, at + 1) as usize;
                if n == 0 {
                    let e = self.new_env(rt, 0);
                    self.set_env(e);
                    return Ok(Control::Eval(self.offset(rt, at + 2)));
                }
                let saved = self.save(rt);
                self.frames.push(Frame::LetInit {
                    let_: at,
                    collected: 0,
                    saved,
                });
                Ok(Control::Eval(self.offset(rt, at + 3)))
            }
            TAG_FIX => {
                let n = self.offset(rt, at + 1) as usize;
                let e = self.new_env(rt, n);
                self.set_env(e);
                if n == 0 {
                    return Ok(Control::Eval(self.offset(rt, at + 2)));
                }
                // `saved` holds the NEW environment: `letrec*` initialisers are
                // evaluated inside the scope they define.
                let saved = self.save(rt);
                self.frames.push(Frame::FixInit {
                    fix: at,
                    index: 0,
                    saved,
                });
                Ok(Control::Eval(self.offset(rt, at + 3)))
            }
            TAG_LAMBDA => {
                let code = self.word(rt, at + 1);
                let env = self.env();
                let c = rt.heap.alloc(ObjType::Closure, 2, Value::UNSPECIFIED);
                rt.heap.obj_set(c, 0, code);
                rt.heap.obj_set(c, 1, env);
                self.set_acc(c);
                Ok(Control::Return)
            }
            TAG_APP => {
                let saved = self.save(rt);
                self.frames.push(Frame::AppArg {
                    app: at,
                    collected: 0,
                    saved,
                });
                Ok(Control::Eval(self.offset(rt, at + 2)))
            }
            other => rt.fail(&format!("unknown node tag {other}"), &[]),
        }
    }

    fn unbound_local(&mut self, rt: &mut Runtime, name: Value) -> Outcome<Control> {
        let text = if rt.heap.is_a(name, ObjType::Symbol) {
            rt.heap.symbol_name(name)
        } else {
            "a variable".to_string()
        };
        rt.fail(&format!("{text} is used before it is defined"), &[])
    }

    fn resume(&mut self, rt: &mut Runtime, p: &mut Prepared, frame: Frame) -> Outcome<Control> {
        if let Some(slot) = frame.saved() {
            self.restore(slot);
        }
        match frame {
            Frame::Halt => unreachable!("handled in drive"),
            Frame::Branch { then, els, saved } => {
                self.stack.truncate(saved as usize);
                Ok(Control::Eval(if self.acc().is_true() { then } else { els }))
            }
            Frame::SeqNext { seq, index, saved } => {
                let n = self.offset(rt, seq + 1);
                let i = index;
                if i + 1 >= n {
                    // The last element is a tail position: drop our slots so a
                    // loop through `begin` does not grow the value stack.
                    self.stack.truncate(saved as usize);
                    return Ok(Control::Eval(self.offset(rt, seq + 2 + i)));
                }
                self.frames.push(Frame::SeqNext {
                    seq,
                    index: i + 1,
                    saved,
                });
                Ok(Control::Eval(self.offset(rt, seq + 2 + i)))
            }
            Frame::AssignLocal { node, saved } => {
                let depth = self.offset(rt, node + 1);
                let index = self.offset(rt, node + 2);
                let v = self.acc();
                self.assign(rt, depth, index, v);
                self.stack.truncate(saved as usize);
                self.set_acc(Value::UNSPECIFIED);
                Ok(Control::Return)
            }
            Frame::AssignGlobal { slot, saved } => {
                let v = self.acc();
                rt.heap.set_global(slot as usize, v);
                self.stack.truncate(saved as usize);
                self.set_acc(Value::UNSPECIFIED);
                Ok(Control::Return)
            }
            Frame::LetInit {
                let_,
                collected,
                saved,
            } => {
                let n = self.offset(rt, let_ + 1);
                let acc = self.acc();
                self.stack.push(acc);
                let done = collected + 1;
                if done < n {
                    self.frames.push(Frame::LetInit {
                        let_,
                        collected: done,
                        saved,
                    });
                    return Ok(Control::Eval(self.offset(rt, let_ + 3 + done)));
                }
                let base = saved as usize + SAVED_SLOTS;
                let e = self.new_env(rt, n as usize);
                for i in 0..n as usize {
                    let v = self.stack[base + i];
                    rt.heap.obj_set(e, i + 1, v);
                }
                self.stack.truncate(saved as usize);
                self.set_env(e);
                Ok(Control::Eval(self.offset(rt, let_ + 2)))
            }
            Frame::FixInit { fix, index, saved } => {
                let n = self.offset(rt, fix + 1);
                let e = self.stack[saved as usize];
                let v = self.acc();
                rt.heap.obj_set(e, index as usize + 1, v);
                let done = index + 1;
                if done < n {
                    self.frames.push(Frame::FixInit {
                        fix,
                        index: done,
                        saved,
                    });
                    return Ok(Control::Eval(self.offset(rt, fix + 3 + done)));
                }
                self.stack.truncate(saved as usize);
                self.set_env(e);
                Ok(Control::Eval(self.offset(rt, fix + 2)))
            }
            Frame::AppArg {
                app,
                collected,
                saved,
            } => {
                let n = self.offset(rt, app + 1);
                let acc = self.acc();
                self.stack.push(acc);
                let done = collected + 1;
                if done <= n {
                    self.frames.push(Frame::AppArg {
                        app,
                        collected: done,
                        saved,
                    });
                    return Ok(Control::Eval(self.offset(rt, app + 2 + done)));
                }
                self.apply(rt, p, saved as usize + SAVED_SLOTS)
            }
            Frame::Consume { saved } => {
                let consumer = self.stack[saved as usize + SAVED_SLOTS];
                let produced = self.acc();
                // The consumer call goes where the consumer was parked, so that
                // `apply` — which reclaims `base - SAVED_SLOTS` — takes this
                // frame's own slots with it. Starting the call any higher would
                // strand `[env, code, consumer]` on the stack, and since no
                // frame is pushed for a consumer call, nothing later would
                // reclaim them: they would be read as extra arguments by
                // whatever application was still pending underneath.
                let call_base = saved as usize + SAVED_SLOTS;
                self.stack.truncate(call_base);
                self.stack.push(consumer);
                self.spread_values(rt, produced);
                self.apply(rt, p, call_base)
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

    // ------------------------------------------------------------- apply
    /// `stack[base]` is the operator; `stack[base+1..]` the arguments. On
    /// return the stack is truncated to the caller's saved slots, because no
    /// frame is pushed: that is what makes tail calls proper.
    fn apply(&mut self, rt: &mut Runtime, p: &mut Prepared, base: usize) -> Outcome<Control> {
        self.safepoint(rt);
        let drop_to = base.saturating_sub(SAVED_SLOTS);
        let f = self.stack[base];
        let argc = self.stack.len() - base - 1;
        match rt.heap.obj_type(f) {
            Some(ObjType::Closure) => {
                let code = rt.heap.obj_ref(f, 0);
                let nparams = rt.heap.bloblet_slot(code, CODE_ARITY).as_fixnum() as usize;
                let has_rest = rt.heap.bloblet_slot(code, CODE_HAS_REST).is_true();
                if !(argc == nparams || (has_rest && argc >= nparams)) {
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
                    return rt.fail(
                        &format!("{label} expects {expected} argument(s), got {argc}"),
                        &[],
                    );
                }
                let closure_env = rt.heap.obj_ref(f, 1);
                let slots = nparams + usize::from(has_rest);
                let e = rt
                    .heap
                    .alloc(ObjType::Vector, slots + 1, Value::UNSPECIFIED);
                rt.heap.obj_set(e, 0, closure_env);
                for i in 0..nparams {
                    let v = self.stack[base + 1 + i];
                    rt.heap.obj_set(e, i + 1, v);
                }
                if has_rest {
                    let extra: Vec<Value> = self.stack[base + 1 + nparams..].to_vec();
                    let rest = rt.heap.list_from(&extra);
                    rt.heap.obj_set(e, nparams + 1, rest);
                }
                let entry = rt.heap.bloblet_slot(code, CODE_ENTRY).as_fixnum() as u32;
                self.stack.truncate(drop_to);
                self.set_env(e);
                self.set_code(code);
                Ok(Control::Eval(entry))
            }
            Some(ObjType::Primitive) => {
                let index = rt.heap.obj_ref(f, 1).as_fixnum() as u16;
                let def = prim::def(index);
                if !def.accepts(argc) {
                    return rt.fail(&format!("{} got {argc} argument(s)", def.name), &[]);
                }
                match def.kind {
                    PrimKind::Simple(func) => {
                        let result = func(rt, &mut self.stack[base + 1..]);
                        self.stack.truncate(drop_to);
                        self.set_acc(result?);
                        Ok(Control::Return)
                    }
                    PrimKind::Engine(op) => self.engine_op(rt, p, op, base),
                }
            }
            Some(ObjType::Continuation) => {
                let vals: Vec<Value> = self.stack[base + 1..].to_vec();
                // Winding is the prelude's business: it knows which extents
                // are being left and entered, and runs their thunks before
                // handing back to `%throw`. Until the prelude has defined the
                // hook, a continuation is reinstated raw.
                if let Some(hook) = p.global(&mut rt.heap, "%continuation-apply") {
                    let list = rt.heap.list_from(&vals);
                    self.stack.truncate(base);
                    self.stack.push(hook);
                    self.stack.push(f);
                    self.stack.push(list);
                    return self.apply(rt, p, base);
                }
                let value = if argc == 1 { vals[0] } else { self.make_values(rt, &vals) };
                self.throw(rt, f, value, base)
            }
            _ => {
                self.stack.truncate(drop_to);
                rt.fail("attempt to call a non-procedure", &[f])
            }
        }
    }

    fn engine_op(
        &mut self,
        rt: &mut Runtime,
        p: &mut Prepared,
        op: EngineOp,
        base: usize,
    ) -> Outcome<Control> {
        let drop_to = base.saturating_sub(SAVED_SLOTS);
        match op {
            // (apply f a b … list)
            EngineOp::Apply => {
                let argc = self.stack.len() - base - 1;
                if argc == 0 {
                    return rt.fail("apply needs a procedure", &[]);
                }
                let f = self.stack[base + 1];
                let last = self.stack[self.stack.len() - 1];
                let Some(tail) = rt.heap.list_to_vec(last) else {
                    return rt.type_error("a proper list as apply's last argument", last);
                };
                let middle: Vec<Value> = self.stack[base + 2..self.stack.len() - 1].to_vec();
                self.stack.truncate(base);
                self.stack.push(f);
                self.stack.extend_from_slice(&middle);
                self.stack.extend_from_slice(&tail);
                self.apply(rt, p, base)
            }
            // (%call/cc f): raw capture, with no dynamic-wind awareness. The
            // prelude wraps this to add winding.
            EngineOp::CallCC => {
                let f = self.stack[base + 1];
                let k = self.capture(rt, drop_to);
                self.stack.truncate(base);
                self.stack.push(f);
                self.stack.push(k);
                self.apply(rt, p, base)
            }
            // ---- marks, prompts, composable continuations ----
            //
            // In this engine the continuation of an application is always the
            // top frame with the value stack at `drop_to`, so that is the
            // (depth, height) a mark or prompt records.
            EngineOp::WithMark => {
                let (key, val, thunk) = (self.stack[base + 1], self.stack[base + 2], self.stack[base + 3]);
                self.marks.set_mark(self.frames.len() as u32, drop_to as u32, key, val);
                self.call_thunk(rt, p, base, thunk)
            }
            EngineOp::Wind => {
                let (winder, thunk) = (self.stack[base + 1], self.stack[base + 2]);
                self.marks.push_winder(self.frames.len() as u32, drop_to as u32, winder);
                self.call_thunk(rt, p, base, thunk)
            }
            EngineOp::Prompt => {
                let (tag, handler, thunk) = (self.stack[base + 1], self.stack[base + 2], self.stack[base + 3]);
                self.marks.push_prompt(self.frames.len() as u32, drop_to as u32, tag, handler);
                self.call_thunk(rt, p, base, thunk)
            }
            EngineOp::CurrentMarks => {
                let from = self.marks.visible_from(self.stack[base + 1]);
                let v = self.marks.mark_list(&mut rt.heap, from);
                self.stack.truncate(drop_to);
                self.set_acc(v);
                Ok(Control::Return)
            }
            EngineOp::FirstMark => {
                let (key, default, tag) = (self.stack[base + 1], self.stack[base + 2], self.stack[base + 3]);
                let from = self.marks.visible_from(tag);
                let v = self.marks.first(from, key).unwrap_or(default);
                self.stack.truncate(drop_to);
                self.set_acc(v);
                Ok(Control::Return)
            }
            EngineOp::CurrentWinders => {
                let v = self.marks.winder_list(&mut rt.heap);
                self.stack.truncate(drop_to);
                self.set_acc(v);
                Ok(Control::Return)
            }
            EngineOp::PromptAvailable => {
                let v = Value::boolean(self.marks.find_prompt(self.stack[base + 1]).is_some());
                self.stack.truncate(drop_to);
                self.set_acc(v);
                Ok(Control::Return)
            }
            EngineOp::Abort => {
                let (tag, vals, step) = (self.stack[base + 1], self.stack[base + 2], self.stack[base + 3]);
                let Some(pi) = self.marks.find_prompt(tag) else {
                    self.stack.truncate(drop_to);
                    return rt.fail("abort-current-continuation: no prompt with that tag", &[tag]);
                };
                self.abort_to(rt, p, pi, tag, vals, step)
            }
            EngineOp::CallComposable => {
                let (f, tag) = (self.stack[base + 1], self.stack[base + 2]);
                let Some(pi) = self.marks.find_prompt(tag) else {
                    self.stack.truncate(drop_to);
                    return rt.fail("call-with-composable-continuation: no prompt with that tag", &[tag]);
                };
                let k = self.capture_composable(rt, drop_to, pi);
                self.stack.truncate(base);
                self.stack.push(f);
                self.stack.push(k);
                self.apply(rt, p, base)
            }
            EngineOp::Host => {
                let request: Vec<Value> = self.stack[base + 1..].to_vec();
                let request = rt.heap.list_from(&request);
                self.pending_host = Some(drop_to);
                Err(Thrown::suspend(request))
            }
            EngineOp::Throw => {
                let (k, vals) = (self.stack[base + 1], self.stack[base + 2]);
                if !rt.heap.is_a(k, ObjType::Continuation) {
                    self.stack.truncate(drop_to);
                    return rt.type_error("a continuation", k);
                }
                let Some(items) = rt.heap.list_to_vec(vals) else {
                    self.stack.truncate(drop_to);
                    return rt.type_error("a list of values", vals);
                };
                let value = self.make_values(rt, &items);
                self.throw(rt, k, value, base)
            }
            EngineOp::Values => {
                let vals: Vec<Value> = self.stack[base + 1..].to_vec();
                self.stack.truncate(drop_to);
                let v = self.make_values(rt, &vals);
                self.set_acc(v);
                Ok(Control::Return)
            }
            // `(%hole POSITION TOTAL)` — describe the pending work, capture
            // it, and hand both to the top level instead of computing.
            EngineOp::Hole => {
                let top = p.global(&mut rt.heap, "%toplevel-tag");
                let step = p.global(&mut rt.heap, "%abort-step");
                let prompt = top.and_then(|t| self.marks.find_prompt(t));
                let floor = prompt.map_or(0, |i| self.marks.meta[i].depth as usize);
                let report = self.describe_context(rt, floor);
                if let (Some(tag), Some(step), Some(pi)) = (top, step, prompt) {
                    // A composable continuation up to the top level's prompt:
                    // exactly the rest of this form, and nothing of the REPL.
                    let k = self.capture_composable(rt, drop_to, pi);
                    let hole = cmarks::make_hole(&mut rt.heap, tag, k, &report, self.stack[base + 1], self.stack[base + 2]);
                    let vals = rt.heap.list_from(&[hole]);
                    return self.abort_to(rt, p, pi, tag, vals, step);
                }
                // No top-level prompt — the prelude is still loading, or this
                // is a bare session. Report and stop, as before.
                self.stack.truncate(drop_to);
                let obj = rt.error_object(&report, &[]);
                // Fatal, so it escapes any handler: a question should not be
                // caught by the program's own error handling and turned into a
                // value.
                Err(Thrown::fatal(obj))
            }
            EngineOp::CallWithValues => {
                let producer = self.stack[base + 1];
                let consumer = self.stack[base + 2];
                self.stack.truncate(drop_to);
                let saved = self.save(rt);
                self.stack.push(consumer);
                self.frames.push(Frame::Consume { saved });
                // `apply` reclaims the caller's saved slots, so the producer
                // call needs its own; without them the truncation would take
                // the consumer with it.
                let inner = self.save(rt);
                let call_base = inner as usize + SAVED_SLOTS;
                self.stack.push(producer);
                self.apply(rt, p, call_base)
            }
        }
    }

    // ------------------------------------------------------------- the hole
    /// Describe what the machine was in the middle of doing.
    ///
    /// This is what a *dynamic* answer buys over a static one. The static
    /// version can say the hole wants an `int`; this one can say that the
    /// operator is `vector-ref`, that its first argument already evaluated to
    /// `#(0 0 0)`, and that the result was going to be the test of an `if` —
    /// facts about values, not about types, and therefore available in Scheme,
    /// which has no types to consult.
    ///
    /// The frames are read from the innermost outwards, which is the order the
    /// work will resume in.
    fn describe_context(&mut self, rt: &mut Runtime, floor: usize) -> String {
        use std::fmt::Write as _;
        let mut out = String::from("evaluation reached a hole");
        let mut depth = 0usize;
        // Frames below `floor` belong to the top level's own machinery, which
        // is not part of the form being asked about.
        for frame in self.frames[floor.min(self.frames.len())..].to_vec().iter().rev() {
            if depth >= 6 {
                out.push_str("\n  …");
                break;
            }
            // A node offset is only meaningful against the code object it came
            // from, and the frames below the innermost one belong to *callers*,
            // with node vectors of their own. The frame convention already
            // saves that code on the value stack, so read each frame's nodes
            // through its own `saved + 1` rather than through the register.
            let code = match frame.saved() {
                Some(saved) => match self.stack.get(saved as usize + 1) {
                    Some(&c) if rt.heap.is_a(c, ObjType::Code) => c,
                    _ => continue,
                },
                None => break,
            };
            let line = match *frame {
                Frame::Halt => break,
                Frame::AppArg { app, collected, saved } => {
                    Some(self.describe_application(rt, code, app, collected, saved))
                }
                Frame::Branch { .. } => {
                    Some("the value is the test of an `if`".to_string())
                }
                Frame::SeqNext { .. } => {
                    Some("the value is discarded by a `begin`".to_string())
                }
                Frame::LetInit { let_, collected, saved: _ } => {
                    let n = self.offset_in(rt, code, let_ + 1);
                    Some(format!(
                        "the value is initialiser {} of {n} in a `let`",
                        collected + 1
                    ))
                }
                Frame::FixInit { fix, index, saved: _ } => {
                    let n = self.offset_in(rt, code, fix + 1);
                    Some(format!(
                        "the value is initialiser {} of {n} in a `letrec`",
                        index + 1
                    ))
                }
                Frame::AssignLocal { .. } | Frame::AssignGlobal { .. } => {
                    Some("the value is being assigned to a variable".to_string())
                }
                Frame::Consume { .. } => {
                    Some("the value is produced for `call-with-values`".to_string())
                }
            };
            if let Some(line) = line {
                let _ = write!(out, "\n  {line}");
                depth += 1;
            }
        }
        out
    }

    /// A node word read against a given code object rather than the register.
    fn offset_in(&self, rt: &Runtime, code: Value, at: u32) -> u32 {
        if at as usize >= fixpt_core::lower::code_items(&rt.heap, code) {
            return 0;
        }
        fixpt_core::lower::code_item(&rt.heap, code, at as usize).as_fixnum() as u32
    }

    /// The application the hole is an argument of, with the arguments that have
    /// already been evaluated.
    fn describe_application(
        &self,
        rt: &Runtime,
        code: Value,
        app: u32,
        collected: u32,
        saved: u32,
    ) -> String {
        use std::fmt::Write as _;
        let total = self.offset_in(rt, code, app + 1);
        let base = saved as usize + SAVED_SLOTS;
        // `collected` counts the operator, so the hole is argument `collected`.
        let position = collected;
        let mut out = String::new();
        if position == 0 {
            let _ = write!(out, "the hole is the operator of a call of {total} argument(s)");
            return out;
        }
        let operator = self.stack.get(base).copied().unwrap_or(Value::UNSPECIFIED);
        let _ = write!(
            out,
            "the hole is argument {position} of {total} to {}",
            fixpt_runtime::write_value(&rt.heap, operator)
        );
        for i in 1..position as usize {
            if let Some(v) = self.stack.get(base + i) {
                let _ = write!(
                    out,
                    "\n    argument {i} evaluated to {}",
                    fixpt_runtime::write_value(&rt.heap, *v)
                );
            }
        }
        out
    }

    // -------------------------------------------------------- continuations
    /// Capture the machine state. The value stack is copied into a heap vector
    /// and the frame stack into a bytevector — frames hold no references, so
    /// this is a straight word copy and the result is an ordinary heap object.
    /// The marks go with it: they are as much a part of the continuation as
    /// the frames they are attached to.
    fn capture(&mut self, rt: &mut Runtime, upto: usize) -> Value {
        let live = &self.stack[..upto];
        let saved_stack = rt.heap.vector_from(live);
        let saved_frames = encode_frames(rt, self.frames.iter().copied());
        let marks = self.marks.encode(&mut rt.heap, 0, 0, 0);
        cmarks::make_continuation(&mut rt.heap, saved_stack, saved_frames, marks, false)
    }

    /// Capture the continuation from the prompt at mark entry `pi` up to here,
    /// as a composable continuation: a segment stored relative to its own
    /// bottom, so that it can be reinstated on top of any other continuation.
    ///
    /// The prompt's frame is not part of it. Its depth and height say where the
    /// continuation *outside* the prompt stood, and everything above them —
    /// frames, stack and marks — is what the prompt delimits.
    fn capture_composable(&mut self, rt: &mut Runtime, upto: usize, pi: usize) -> Value {
        let m = self.marks.meta[pi];
        let (depth, height) = (m.depth as usize, m.height as usize);
        let saved_stack = rt.heap.vector_from(&self.stack[height..upto]);
        let frames = self.frames[depth..].iter().map(|f| f.rebase(height as u32, 0));
        let saved_frames = encode_frames(rt, frames);
        let marks = self.marks.encode(&mut rt.heap, pi + 1, m.depth, m.height);
        cmarks::make_continuation(&mut rt.heap, saved_stack, saved_frames, marks, true)
    }

    /// Deliver `value` to continuation `k`, from an application at `base`.
    ///
    /// A full continuation *replaces* the machine. A composable one is laid on
    /// top of the continuation of this application — which in this engine is
    /// the top frame with the stack at `drop_to` — with every recorded position
    /// moved to where it now sits. After that both are an ordinary return.
    fn throw(&mut self, rt: &mut Runtime, k: Value, value: Value, base: usize) -> Outcome<Control> {
        if cmarks::is_composable(&rt.heap, k) {
            let at = base.saturating_sub(SAVED_SLOTS);
            self.stack.truncate(at);
            let depth = self.frames.len() as u32;
            let seg = rt.heap.obj_ref(k, cmarks::K_STACK);
            for i in 0..rt.heap.obj_len(seg) {
                let v = rt.heap.obj_ref(seg, i);
                self.stack.push(v);
            }
            for f in decode_frames(rt, rt.heap.obj_ref(k, cmarks::K_FRAMES)) {
                self.frames.push(f.rebase(0, at as u32));
            }
            let (vals, meta) = (rt.heap.obj_ref(k, cmarks::K_MARK_VALS), rt.heap.obj_ref(k, cmarks::K_MARK_META));
            self.marks.append_encoded(&rt.heap, vals, meta, depth, at as u32);
        } else {
            self.restore_continuation(rt, k);
        }
        self.set_acc(value);
        Ok(Control::Return)
    }

    fn restore_continuation(&mut self, rt: &mut Runtime, k: Value) {
        let saved_stack = rt.heap.obj_ref(k, cmarks::K_STACK);
        self.stack.clear();
        for i in 0..rt.heap.obj_len(saved_stack) {
            let v = rt.heap.obj_ref(saved_stack, i);
            self.stack.push(v);
        }
        self.frames = decode_frames(rt, rt.heap.obj_ref(k, cmarks::K_FRAMES));
        self.marks.clear();
        let (vals, meta) = (rt.heap.obj_ref(k, cmarks::K_MARK_VALS), rt.heap.obj_ref(k, cmarks::K_MARK_META));
        self.marks.append_encoded(&rt.heap, vals, meta, 0, 0);
    }

    /// Call `thunk` with no arguments as the continuation of the application at
    /// `base` — a tail call, so a mark just attached to that continuation is
    /// the one the thunk's body sees.
    fn call_thunk(&mut self, rt: &mut Runtime, p: &mut Prepared, base: usize, thunk: Value) -> Outcome<Control> {
        self.stack.truncate(base);
        self.stack.push(thunk);
        self.apply(rt, p, base)
    }

    /// Cut the machine back to where mark entry `entry` was made, dropping it
    /// and everything above.
    fn cut_to(&mut self, entry: usize) {
        let m = self.marks.meta[entry];
        self.frames.truncate(m.depth as usize);
        self.stack.truncate(m.height as usize);
        self.marks.truncate(entry);
    }

    /// Abort to the prompt at entry `pi`, delivering `vals` to its handler.
    ///
    /// `dynamic-wind` extents between here and the prompt are left one at a
    /// time, innermost first: cut to the extent's own frame, then call
    /// `(step after tag vals step)` there, whose job is to run `after` and
    /// abort again. So each `after` thunk runs in exactly the dynamic context
    /// of its `dynamic-wind` — with the marks, handlers and outer extents that
    /// were live there, and none of the inner ones.
    fn abort_to(
        &mut self,
        rt: &mut Runtime,
        p: &mut Prepared,
        pi: usize,
        tag: Value,
        vals: Value,
        step: Value,
    ) -> Outcome<Control> {
        if let Some(wi) = self.marks.innermost_winder_above(pi) {
            let after = rt.heap.cdr(self.marks.val(wi));
            self.cut_to(wi);
            let saved = self.save(rt);
            let base = saved as usize + SAVED_SLOTS;
            self.stack.extend_from_slice(&[step, after, tag, vals, step]);
            return self.apply(rt, p, base);
        }
        let handler = self.marks.val(pi);
        let Some(items) = rt.heap.list_to_vec(vals) else {
            return rt.type_error("a list of values", vals);
        };
        self.cut_to(pi);
        let saved = self.save(rt);
        let base = saved as usize + SAVED_SLOTS;
        self.stack.push(handler);
        self.stack.extend_from_slice(&items);
        self.apply(rt, p, base)
    }

    fn make_values(&mut self, rt: &mut Runtime, vals: &[Value]) -> Value {
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

    // ------------------------------------------------------- environments
    fn new_env(&mut self, rt: &mut Runtime, slots: usize) -> Value {
        let parent = self.env();
        let e = rt.heap.alloc(ObjType::Vector, slots + 1, Value::UNBOUND);
        rt.heap.obj_set(e, 0, parent);
        e
    }

    fn lookup(&self, rt: &Runtime, depth: u32, index: u32) -> Value {
        let mut e = self.env();
        for _ in 0..depth {
            e = rt.heap.obj_ref(e, 0);
        }
        rt.heap.obj_ref(e, index as usize + 1)
    }

    fn assign(&mut self, rt: &mut Runtime, depth: u32, index: u32, v: Value) {
        let mut e = self.env();
        for _ in 0..depth {
            e = rt.heap.obj_ref(e, 0);
        }
        rt.heap.obj_set(e, index as usize + 1, v);
    }

    // ---------------------------------------------------------- safepoint
    /// The only place a collection can happen. Every live value is in `stack`
    /// or in `regs` — the program's code is reachable from the code register
    /// and from the heap roots, so there is no third root set to remember.
    fn safepoint(&mut self, rt: &mut Runtime) {
        self.regs[REG_SCRATCH] = Value::UNSPECIFIED;
        rt.heap
            .maybe_collect(&mut [&mut self.stack, &mut self.regs, &mut self.marks.vals]);
    }
}

fn encode_frames(rt: &mut Runtime, frames: impl Iterator<Item = Frame>) -> Value {
    let mut bytes = Vec::new();
    for f in frames {
        for w in f.encode() {
            bytes.extend_from_slice(&w.to_le_bytes());
        }
    }
    rt.heap.make_bytevector(&bytes)
}

fn decode_frames(rt: &Runtime, v: Value) -> Vec<Frame> {
    rt.heap
        .bytevector_to_vec(v)
        .chunks_exact(FRAME_WORDS * 8)
        .map(|chunk| {
            let mut w = [0u64; FRAME_WORDS];
            for (i, word) in chunk.chunks_exact(8).enumerate() {
                w[i] = u64::from_le_bytes(word.try_into().expect("8 bytes"));
            }
            Frame::decode(w).expect("frames we encoded ourselves")
        })
        .collect()
}
