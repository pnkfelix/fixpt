//! The AST machine — the interpreted engine.
//!
//! An explicit-stack machine over the Core IR, not a recursive tree walk. Three
//! things follow from that choice, and all three are requirements rather than
//! refinements:
//!
//! * **Proper tail calls.** Applying a procedure never pushes a frame — the
//!   caller's pending work is already a frame, or there is none. So a tail call
//!   is simply "build the new environment and keep going", and a loop written
//!   as tail recursion runs in constant space, as R7RS requires.
//! * **Unbounded recursion depth.** Scheme recursion consumes the machine's own
//!   `Vec`s, not the Rust call stack, so a deeply recursive program reports out
//!   of memory rather than segfaulting.
//! * **Re-entrant `call/cc`.** A continuation is a copy of the value stack and
//!   an encoding of the frame stack. Because frames hold no heap references,
//!   that encoding is just words, and a captured continuation is an ordinary
//!   heap object that survives collection and heap dumping.
//!
//! Collection happens only at [`Interp::safepoint`], which is reached on every
//! procedure application. Everything live at that moment is in `stack`, in
//! `regs`, or in the program's constant pool, and all three are handed to the
//! collector explicitly.

use crate::frame::{Frame, FRAME_WORDS};
use crate::prepare::Prepared;
use fixpt_core::ir::{LambdaId, Node, NodeId};
use fixpt_heap::{ObjType, Value};
use fixpt_runtime::error::{Outcome, Thrown};
use fixpt_runtime::prim::{self, EngineOp, PrimKind};
use fixpt_runtime::Runtime;

/// Register file. Kept as one slice so the root set is two contiguous ranges.
const REG_ACC: usize = 0;
const REG_ENV: usize = 1;
const REG_SCRATCH: usize = 2;
const N_REGS: usize = 3;

enum Control {
    Eval(NodeId),
    /// `acc` holds a value; resume the top frame.
    Return,
}

pub struct Interp {
    stack: Vec<Value>,
    frames: Vec<Frame>,
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

    /// Run a prepared program to completion.
    pub fn run(&mut self, rt: &mut Runtime, p: &mut Prepared) -> Outcome<Value> {
        self.stack.clear();
        self.frames.clear();
        self.frames.push(Frame::Halt);
        self.set_env(Value::FALSE);
        self.set_acc(Value::UNSPECIFIED);
        self.steps = 0;
        let body = p.program.body;
        self.drive(rt, p, Control::Eval(body))
    }

    /// Apply a procedure from native code, running it to completion.
    pub fn call(&mut self, rt: &mut Runtime, p: &mut Prepared, f: Value, args: &[Value]) -> Outcome<Value> {
        self.stack.clear();
        self.frames.clear();
        self.frames.push(Frame::Halt);
        self.set_env(Value::FALSE);
        self.steps = 0;
        self.save_env();
        let base = self.stack.len();
        self.stack.push(f);
        self.stack.extend_from_slice(args);
        let control = self.apply(rt, p, base)?;
        self.drive(rt, p, control)
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

    /// A primitive raised. Unless the condition is already past the handler
    /// chain, hand it to the prelude's `raise`, so user handlers installed with
    /// `with-exception-handler` get their chance. This is the only place the
    /// engine knows anything at all about the condition system.
    fn dispatch_condition(
        &mut self,
        rt: &mut Runtime,
        p: &mut Prepared,
        t: Thrown,
    ) -> Outcome<Option<Control>> {
        if t.fatal {
            return Ok(None);
        }
        let Some(raise) = p.raise_procedure(rt) else { return Ok(None) };
        // Same reason as in `CallWithValues`: `apply` reclaims `base - 1`.
        self.save_env();
        let base = self.stack.len();
        self.stack.push(raise);
        self.stack.push(t.obj);
        Ok(Some(self.apply(rt, p, base)?))
    }

    // ------------------------------------------------------------ evaluation
    fn eval(&mut self, rt: &mut Runtime, p: &mut Prepared, node: NodeId) -> Outcome<Control> {
        match p.program.node(node).clone() {
            Node::Const(c) => {
                let v = p.program.constant(c);
                self.set_acc(v);
                Ok(Control::Return)
            }
            Node::Ref(_) => {
                let a = p.addressing.get(node);
                let v = self.lookup(rt, a.depth, a.index);
                if v.is_unbound() {
                    let name = p.var_name(rt, node);
                    return rt.fail(&format!("{name} is used before it is defined"), &[]);
                }
                self.set_acc(v);
                Ok(Control::Return)
            }
            Node::GlobalRef(g) => {
                let v = rt.heap.global(g.index());
                if v.is_unbound() {
                    let name = p.global_name(rt, g);
                    return rt.fail(&format!("unbound variable: {name}"), &[]);
                }
                self.set_acc(v);
                Ok(Control::Return)
            }
            Node::Set(_, e) => {
                let env_slot = self.save_env();
                self.frames.push(Frame::AssignLocal { node, env_slot });
                Ok(Control::Eval(e))
            }
            Node::GlobalSet(g, e) => {
                let env_slot = self.save_env();
                self.frames.push(Frame::AssignGlobal { slot: g.0, env_slot });
                Ok(Control::Eval(e))
            }
            Node::If(test, then, els) => {
                let env_slot = self.save_env();
                self.frames.push(Frame::Branch { then, els, env_slot });
                Ok(Control::Eval(test))
            }
            Node::Seq(items) => {
                let env_slot = self.save_env();
                self.frames.push(Frame::SeqNext { seq: node, index: 1, env_slot });
                Ok(Control::Eval(items[0]))
            }
            Node::Let { vars, inits, body } => {
                if inits.is_empty() {
                    let e = self.new_env(rt, vars.len());
                    self.set_env(e);
                    return Ok(Control::Eval(body));
                }
                let env_slot = self.save_env();
                self.frames.push(Frame::LetInit { let_: node, collected: 0, env_slot });
                Ok(Control::Eval(inits[0]))
            }
            Node::Fix { vars, inits, body } => {
                let e = self.new_env(rt, vars.len());
                self.set_env(e);
                if inits.is_empty() {
                    return Ok(Control::Eval(body));
                }
                // `env_slot` holds the NEW environment: `letrec*` initialisers
                // are evaluated inside the scope they define.
                let env_slot = self.save_env();
                self.frames.push(Frame::FixInit { fix: node, index: 0, env_slot });
                Ok(Control::Eval(inits[0]))
            }
            Node::Lambda(l) => {
                let v = self.make_closure(rt, p, l);
                self.set_acc(v);
                Ok(Control::Return)
            }
            Node::App { rator, .. } => {
                let env_slot = self.save_env();
                self.frames.push(Frame::AppArg { app: node, collected: 0, env_slot });
                Ok(Control::Eval(rator))
            }
            Node::PrimCall { .. } => {
                // Produced only by an optimisation pass the interpreter does
                // not run; the compiler is where it belongs.
                rt.fail("PrimCall is not used by the AST engine", &[])
            }
        }
    }

    fn resume(&mut self, rt: &mut Runtime, p: &mut Prepared, frame: Frame) -> Outcome<Control> {
        if let Some(slot) = frame.env_slot() {
            let e = self.stack[slot as usize];
            self.set_env(e);
        }
        match frame {
            Frame::Halt => unreachable!("handled in drive"),
            Frame::Branch { then, els, env_slot } => {
                self.stack.truncate(env_slot as usize);
                Ok(Control::Eval(if self.acc().is_true() { then } else { els }))
            }
            Frame::SeqNext { seq, index, env_slot } => {
                let Node::Seq(items) = p.program.node(seq).clone() else {
                    unreachable!("SeqNext refers to a Seq node")
                };
                let i = index as usize;
                if i + 1 >= items.len() {
                    // Last element is a tail position: drop our stack slot so a
                    // loop through `begin` does not grow the value stack.
                    self.stack.truncate(env_slot as usize);
                    return Ok(Control::Eval(items[i]));
                }
                self.frames.push(Frame::SeqNext { seq, index: index + 1, env_slot });
                Ok(Control::Eval(items[i]))
            }
            Frame::AssignLocal { node, env_slot } => {
                let a = p.addressing.get(node);
                let v = self.acc();
                self.assign(rt, a.depth, a.index, v);
                self.stack.truncate(env_slot as usize);
                self.set_acc(Value::UNSPECIFIED);
                Ok(Control::Return)
            }
            Frame::AssignGlobal { slot, env_slot } => {
                let v = self.acc();
                rt.heap.set_global(slot as usize, v);
                self.stack.truncate(env_slot as usize);
                self.set_acc(Value::UNSPECIFIED);
                Ok(Control::Return)
            }
            Frame::LetInit { let_, collected, env_slot } => {
                let Node::Let { vars, inits, body } = p.program.node(let_).clone() else {
                    unreachable!("LetInit refers to a Let node")
                };
                let acc = self.acc();
                self.stack.push(acc);
                let n = collected as usize + 1;
                if n < inits.len() {
                    self.frames.push(Frame::LetInit { let_, collected: n as u32, env_slot });
                    return Ok(Control::Eval(inits[n]));
                }
                let base = env_slot as usize + 1;
                let e = self.new_env(rt, vars.len());
                for i in 0..vars.len() {
                    let v = self.stack[base + i];
                    rt.heap.obj_set(e, i + 1, v);
                }
                self.stack.truncate(env_slot as usize);
                self.set_env(e);
                Ok(Control::Eval(body))
            }
            Frame::FixInit { fix, index, env_slot } => {
                let Node::Fix { inits, body, .. } = p.program.node(fix).clone() else {
                    unreachable!("FixInit refers to a Fix node")
                };
                let e = self.stack[env_slot as usize];
                let v = self.acc();
                rt.heap.obj_set(e, index as usize + 1, v);
                let n = index as usize + 1;
                if n < inits.len() {
                    self.frames.push(Frame::FixInit { fix, index: n as u32, env_slot });
                    return Ok(Control::Eval(inits[n]));
                }
                self.stack.truncate(env_slot as usize);
                self.set_env(e);
                Ok(Control::Eval(body))
            }
            Frame::AppArg { app, collected, env_slot } => {
                let (rator, rands) = match p.program.node(app).clone() {
                    Node::App { rator, rands } => (rator, rands),
                    _ => unreachable!("AppArg refers to an App node"),
                };
                let _ = rator;
                let acc = self.acc();
                self.stack.push(acc);
                let n = collected as usize + 1;
                if n <= rands.len() {
                    self.frames.push(Frame::AppArg { app, collected: n as u32, env_slot });
                    return Ok(Control::Eval(rands[n - 1]));
                }
                self.apply(rt, p, env_slot as usize + 1)
            }
            Frame::Consume { env_slot } => {
                let consumer = self.stack[env_slot as usize + 1];
                let produced = self.acc();
                let base = env_slot as usize + 2;
                self.stack.truncate(base);
                self.stack.push(consumer);
                self.spread_values(rt, produced);
                self.apply(rt, p, base)
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
    /// return the stack is truncated to `base - 1` (the caller's saved-env
    /// slot), because no frame is pushed: that is what makes tail calls proper.
    fn apply(&mut self, rt: &mut Runtime, p: &mut Prepared, base: usize) -> Outcome<Control> {
        self.safepoint(rt, p);
        let f = self.stack[base];
        let argc = self.stack.len() - base - 1;
        match rt.heap.obj_type(f) {
            Some(ObjType::Closure) => {
                let code = rt.heap.obj_ref(f, 0);
                let lambda = LambdaId(rt.heap.obj_ref(code, 3).as_fixnum() as u32);
                let info = p.program.lambda(lambda);
                let nparams = info.params.len();
                let has_rest = info.rest.is_some();
                if !(argc == nparams || (has_rest && argc >= nparams)) {
                    let name = info
                        .name
                        .map(|s| rt.interner.name(s).to_string())
                        .unwrap_or_else(|| "procedure".into());
                    let expected = if has_rest {
                        format!("at least {nparams}")
                    } else {
                        nparams.to_string()
                    };
                    return rt.fail(
                        &format!("{name} expects {expected} argument(s), got {argc}"),
                        &[],
                    );
                }
                let body = info.body;
                let closure_env = rt.heap.obj_ref(f, 1);
                let slots = nparams + usize::from(has_rest);
                let e = rt.heap.alloc(ObjType::Vector, slots + 1, Value::UNSPECIFIED);
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
                // Drop the operator, the arguments and the caller's saved env:
                // nothing after this point refers to them.
                self.stack.truncate(base.saturating_sub(1));
                self.set_env(e);
                Ok(Control::Eval(body))
            }
            Some(ObjType::Primitive) => {
                let index = rt.heap.obj_ref(f, 1).as_fixnum() as u16;
                let def = prim::def(index);
                if !def.accepts(argc) {
                    return rt.fail(
                        &format!("{} got {argc} argument(s)", def.name),
                        &[],
                    );
                }
                match def.kind {
                    PrimKind::Simple(func) => {
                        let result = func(rt, &mut self.stack[base + 1..]);
                        self.stack.truncate(base.saturating_sub(1));
                        self.set_acc(result?);
                        Ok(Control::Return)
                    }
                    PrimKind::Engine(op) => self.engine_op(rt, p, op, base),
                }
            }
            Some(ObjType::Continuation) => {
                let value = if argc == 1 {
                    self.stack[base + 1]
                } else {
                    let vals: Vec<Value> = self.stack[base + 1..].to_vec();
                    self.make_values(rt, &vals)
                };
                self.restore_continuation(rt, f, value);
                Ok(Control::Return)
            }
            _ => {
                self.stack.truncate(base.saturating_sub(1));
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
                let k = self.capture(rt, base);
                self.stack.truncate(base);
                self.stack.push(f);
                self.stack.push(k);
                self.apply(rt, p, base)
            }
            EngineOp::Values => {
                let vals: Vec<Value> = self.stack[base + 1..].to_vec();
                self.stack.truncate(base.saturating_sub(1));
                let v = self.make_values(rt, &vals);
                self.set_acc(v);
                Ok(Control::Return)
            }
            EngineOp::CallWithValues => {
                let producer = self.stack[base + 1];
                let consumer = self.stack[base + 2];
                self.stack.truncate(base.saturating_sub(1));
                let env_slot = self.save_env();
                self.stack.push(consumer);
                self.frames.push(Frame::Consume { env_slot });
                // `apply` truncates to `base - 1`, so the producer call needs
                // its own sacrificial saved-env slot; without it the truncation
                // would take the consumer with it.
                self.save_env();
                let inner = self.stack.len();
                self.stack.push(producer);
                self.apply(rt, p, inner)
            }
        }
    }

    // -------------------------------------------------------- continuations
    /// Capture the machine state. The value stack is copied into a heap vector
    /// and the frame stack into a bytevector — frames hold no references, so
    /// this is a straight word copy and the result is an ordinary heap object.
    fn capture(&mut self, rt: &mut Runtime, base: usize) -> Value {
        // Everything below `base` is the continuation; the operator and its
        // argument at `base`… belong to the `%call/cc` call itself.
        let live = &self.stack[..base.saturating_sub(1)];
        let saved_stack = rt.heap.vector_from(live);
        let mut bytes = Vec::with_capacity(self.frames.len() * FRAME_WORDS * 8);
        for f in &self.frames {
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

    fn restore_continuation(&mut self, rt: &mut Runtime, k: Value, value: Value) {
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
            self.frames.push(Frame::decode(w).expect("frames we encoded ourselves"));
        }
        self.set_acc(value);
    }

    fn make_values(&mut self, rt: &mut Runtime, vals: &[Value]) -> Value {
        if vals.len() == 1 {
            return vals[0];
        }
        let v = rt.heap.alloc(ObjType::Values, vals.len(), Value::UNSPECIFIED);
        for (i, x) in vals.iter().enumerate() {
            rt.heap.obj_set(v, i, *x);
        }
        v
    }

    // ------------------------------------------------------- environments
    fn save_env(&mut self) -> u32 {
        let slot = self.stack.len() as u32;
        let e = self.env();
        self.stack.push(e);
        slot
    }

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

    fn make_closure(&mut self, rt: &mut Runtime, p: &Prepared, l: LambdaId) -> Value {
        let code = p.code_for(rt, l);
        let env = self.env();
        let c = rt.heap.alloc(ObjType::Closure, 2, Value::UNSPECIFIED);
        rt.heap.obj_set(c, 0, code);
        rt.heap.obj_set(c, 1, env);
        c
    }

    // ---------------------------------------------------------- safepoint
    /// The only place a collection can happen. Every live value is in `stack`,
    /// in `regs`, or in the constant pool; nothing is in a Rust local across
    /// this call.
    fn safepoint(&mut self, rt: &mut Runtime, p: &mut Prepared) {
        self.regs[REG_SCRATCH] = Value::UNSPECIFIED;
        rt.heap.maybe_collect(&mut [
            &mut self.stack,
            &mut self.regs,
            &mut p.program.consts,
        ]);
    }
}
