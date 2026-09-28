//! Code in the native convention (`docs/research/native-conventions.md`,
//! step 2): first-order procedures compiled from their register code to
//! machine code that calls by `bl` and returns by `ret`, with frames on a
//! stack of its own, and no ip, data stack, return entry or resume table.
//!
//! The convention, as the note has it, with register code's numbering:
//!
//! | what                 | where                                                      |
//! | -------------------- | ---------------------------------------------------------- |
//! | arguments            | `x1`–`x8` (register code's `REG1`…`REG8`)                  |
//! | result               | `x0` (`RESULT`)                                            |
//! | return address       | `x30`, saved in the frame by a procedure that has one      |
//! | frame link           | `x29`                                                      |
//! | the machine's state  | `x24`, pinned                                              |
//! | fuel                 | `x28`, pinned                                              |
//! | values across a call | the frame's slots, `[x29, #16 + 8n]` for slot `n`          |
//!
//! Every register but the pinned ones is the caller's to lose across a
//! call; register code already keeps whatever lives across one in its
//! frame. A procedure with no frame, no call and no loop (a leaf) checks
//! nothing: `(lambda ((x int)) x)` is `mov x0, x1; ret`. One with a frame
//! checks the stack's limit once, on entry, and fuel on entry; a loop
//! checks fuel on its back edge.
//!
//! What is compiled, for now: procedures that capture nothing, whose
//! register code keeps to arguments, immediate constants, registers and
//! frame slots, the integer operations register code does inline, pairs'
//! and bloblets' fields, branches, and calls of themselves or of other such
//! procedures named by globals. Anything else (a call-out, which may
//! collect; a closure made or read; a global read for its value) declines
//! the procedure, and whoever calls it. The collector never runs while
//! this code does, so no frame needs a stack map yet (step 3).
//!
//! A global called is bound when compiling: the code calls the procedure
//! the global held then. That is right for a program whose globals are
//! defined once, which is all this is used for until step 3 gives code
//! bloblets fields to keep their globals in.

use crate::arm64::*;
use crate::codespace::{CodeSpace, Offset};
use fixpt_heap::layout::cellular::{CLOSURE_FREE0, CLOSURE_WORD, ROUTINES, WORD_CELL0, WORD_TWIN};
use fixpt_heap::layout::regcode::OPS;
use fixpt_heap::{Heap, Value};
use std::collections::HashMap;
use std::mem::offset_of;

const RESULT: Reg = 0;
const ST: Reg = 24;
const FUEL: Reg = 28;
const FRAME: Reg = 29;
const LINK: Reg = 30;
const X9: Reg = 9;
const X16: Reg = 16;
const X17: Reg = 17;

/// What code in the native convention shares with the Rust side that runs
/// it: where to go back to, the stack's limit, fuel, and what trapped.
#[repr(C)]
#[derive(Default)]
struct DState {
    rust_sp: u64,
    stack_top: u64,
    stack_limit: u64,
    fuel: u64,
    /// The trap's code (`TRAPS`), 0 if none, and where it was raised.
    trap: u64,
    pc: u64,
    args: [u64; 8],
}

/// The traps this code raises, by code.
const TRAPS: [&str; 4] = ["", "out of fuel", "stack overflow", "integer overflow"];
const OUT_OF_FUEL: u32 = 1;
const STACK_OVERFLOW: u32 = 2;
const OVERFLOW: u32 = 3;

fn st_off(f: usize) -> u32 {
    f as u32
}

/// The native stack: plenty for deep recursion, with room below the limit
/// for the frame that finds it has passed it.
const STACK_WORDS: usize = 1 << 20;
const STACK_SLACK: u64 = 64 * 1024;

#[derive(Copy, Clone)]
struct Label(usize);

/// A branch to a label, made when the label is placed.
#[derive(Copy, Clone)]
enum Fix {
    B,
    Bl,
    If(Cond),
}

/// Instructions with labels, patched when everything is placed.
struct Asm {
    code: Vec<u32>,
    labels: Vec<Option<usize>>,
    fixups: Vec<(usize, Label, Fix)>,
}

impl Asm {
    fn new() -> Asm {
        Asm { code: Vec::new(), labels: Vec::new(), fixups: Vec::new() }
    }
    fn e(&mut self, w: u32) {
        self.code.push(w);
    }
    fn es(&mut self, ws: &[u32]) {
        self.code.extend_from_slice(ws);
    }
    fn label(&mut self) -> Label {
        self.labels.push(None);
        Label(self.labels.len() - 1)
    }
    fn bind(&mut self, l: Label) {
        self.labels[l.0] = Some(self.code.len());
    }
    /// A branch of kind `f` to `l`.
    fn to(&mut self, l: Label, f: Fix) {
        self.fixups.push((self.code.len(), l, f));
        self.code.push(NOP);
    }
    fn finish(mut self) -> Result<Vec<u32>, String> {
        for (at, l, f) in std::mem::take(&mut self.fixups) {
            let to = self.labels[l.0].ok_or("a label never placed")?;
            let d = to as i64 - at as i64;
            self.code[at] = match f {
                Fix::B => b(d),
                Fix::Bl => bl(d),
                Fix::If(c) => b_cond(c, d),
            };
        }
        Ok(self.code)
    }
}

/// A procedure, compiled or being compiled: where its code will start.
struct Proc {
    entry: Label,
}

/// Compiles procedures and runs them.
pub struct DirectMachine {
    space: CodeSpace,
    /// The trampoline from Rust, and the common trap.
    entry: Offset,
    stack: Vec<u64>,
}

/// A run that trapped: what, and where: the address of the stub its site
/// branched to, one per site.
#[derive(Debug, PartialEq)]
pub struct DirectTrap {
    pub what: &'static str,
    pub pc: u64,
}

/// A compiled procedure: where its code is.
#[derive(Copy, Clone, Debug)]
pub struct Compiled {
    pub at: Offset,
    pub len: usize,
    pub arity: usize,
}

impl DirectMachine {
    pub fn new() -> Result<DirectMachine, String> {
        let mut space = CodeSpace::new(8 << 20).map_err(|e| e.to_string())?;
        let code = trampoline();
        let entry = space.alloc(4 * code.len(), 16).ok_or("no room for the trampoline")?;
        space.write_code(entry, &code);
        space.flush(entry, 4 * code.len());
        Ok(DirectMachine { space, entry, stack: vec![0; STACK_WORDS] })
    }

    /// Compile `closure`'s procedure, and every procedure it calls, to code
    /// in the native convention: what it compiled, the first first; or why
    /// it could not.
    pub fn compile(&mut self, heap: &Heap, closure: Value) -> Result<Vec<(String, Compiled)>, String> {
        let mut a = Asm::new();
        let kinds = (0..TRAPS.len()).map(|_| a.label()).collect();
        let mut c = Compiling { heap, a, procs: HashMap::new(), queue: Vec::new(), order: Vec::new(), kinds };
        c.proc_of(closure)?;
        while let Some((word, rw)) = c.queue.pop() {
            c.procedure(word, rw)?;
        }
        // Each trap's code, once for them all: it records the trap and
        // where, and leaves.
        let traps_at = c.a.code.len();
        for code in 1..TRAPS.len() {
            let a = &mut c.a;
            a.bind(c.kinds[code]);
            a.e(movz(X9, code as u32, 0));
            a.e(str(X9, ST, st_off(offset_of!(DState, trap))));
            a.e(sub_imm(X9, LINK, 4));
            a.e(str(X9, ST, st_off(offset_of!(DState, pc))));
            a.e(str(FUEL, ST, st_off(offset_of!(DState, fuel))));
            leave(a);
        }
        let Compiling { a, procs, order, .. } = c;
        let starts: Vec<(String, usize, usize)> =
            order.iter().map(|(w, name, arity)| (name.clone(), a.labels[procs[w].entry.0].expect("placed"), *arity)).collect();
        let code = a.finish()?;
        let at = self.space.alloc(4 * code.len(), 16).ok_or("the code space is full")?;
        self.space.write_code(at, &code);
        self.space.flush(at, 4 * code.len());
        let mut out = Vec::new();
        for (i, (name, start, arity)) in starts.iter().enumerate() {
            let end = starts.get(i + 1).map_or(traps_at, |s| s.1);
            out.push((name.clone(), Compiled { at: at + 4 * start, len: end - start, arity: *arity }));
        }
        Ok(out)
    }

    /// Call `p` with `args`, in at most about `fuel` steps.
    pub fn call(&mut self, p: Compiled, args: &[Value], fuel: u64) -> Result<Value, DirectTrap> {
        assert_eq!(args.len(), p.arity, "the procedure's arity");
        let top = (self.stack.as_mut_ptr() as u64 + 8 * STACK_WORDS as u64) & !15;
        let mut st = DState { stack_top: top, stack_limit: self.stack.as_ptr() as u64 + STACK_SLACK, fuel, ..DState::default() };
        for (i, a) in args.iter().enumerate() {
            st.args[i] = a.raw();
        }
        let target = self.space.exec_addr(p.at) as u64;
        // SAFETY: the trampoline follows the C convention, saves what it
        // must, runs on the stack in `self.stack` (which outlives the call),
        // and touches only the state and that stack; the procedure's code,
        // compiled above, reads only its arguments and what they point to,
        // which the heap's owner keeps still while it runs (it allocates
        // nothing, so nothing collects).
        let r = unsafe { self.space.call(self.entry, [&mut st as *mut DState as u64, target, 0, 0]) };
        if st.trap != 0 {
            return Err(DirectTrap { what: TRAPS[st.trap as usize], pc: st.pc });
        }
        Ok(Value(r))
    }

    /// `p`'s instructions, as they are in the code space.
    pub fn instructions(&self, p: Compiled) -> Vec<u32> {
        (0..p.len).map(|i| self.space.read_u32(p.at + 4 * i)).collect()
    }
}

/// From Rust, `entry(state, procedure)`: the callee-saved registers saved,
/// the native stack entered, the arguments loaded, the procedure called,
/// and back with its value. The common trap follows it: it records the
/// trap and where, and leaves as the trampoline does, through the Rust
/// stack pointer saved in the state.
fn trampoline() -> Vec<u32> {
    let mut a = Asm::new();
    a.e(stp_pre(FRAME, LINK, SP, -96));
    a.e(add_imm(FRAME, SP, 0));
    for (i, r) in [19, 21, 23, 25, 27].iter().enumerate() {
        a.e(stp(*r, *r + 1, SP, 16 + 16 * i as i64));
    }
    a.e(mov(ST, 0));
    a.e(add_imm(X9, SP, 0));
    a.e(str(X9, ST, st_off(offset_of!(DState, rust_sp))));
    a.e(ldr(FUEL, ST, st_off(offset_of!(DState, fuel))));
    a.e(mov(X16, 1));
    a.e(ldr(X9, ST, st_off(offset_of!(DState, stack_top))));
    a.e(add_imm(SP, X9, 0));
    let args = offset_of!(DState, args) as i64;
    for k in 0..4 {
        a.e(ldp(1 + 2 * k, 2 + 2 * k, ST, args + 16 * k as i64));
    }
    a.e(blr(X16));
    a.e(str(FUEL, ST, st_off(offset_of!(DState, fuel))));
    leave(&mut a);
    a.finish().expect("no labels")
}

/// Back to Rust from anywhere on the native stack.
fn leave(a: &mut Asm) {
    a.e(ldr(X9, ST, st_off(offset_of!(DState, rust_sp))));
    a.e(add_imm(SP, X9, 0));
    for (i, r) in [19, 21, 23, 25, 27].iter().enumerate() {
        a.e(ldp(*r, *r + 1, SP, 16 + 16 * i as i64));
    }
    a.e(ldp_post(FRAME, LINK, SP, 96));
    a.e(ret());
}

struct Compiling<'h> {
    heap: &'h Heap,
    a: Asm,
    /// Each procedure by its cellular word.
    procs: HashMap<u64, Proc>,
    /// Those still to compile: the word and its register word.
    queue: Vec<(Value, Value)>,
    /// Every procedure, in the order first seen: name and arity.
    order: Vec<(u64, String, usize)>,
    /// Each trap's common code, by its number.
    kinds: Vec<Label>,
}

impl Compiling<'_> {
    /// The procedure of `closure`, queued to compile if it is new.
    fn proc_of(&mut self, closure: Value) -> Result<Label, String> {
        let h = self.heap;
        if !closure.is_bloblet() || h.bloblet_head(closure).fields < CLOSURE_WORD {
            return Err("a call of something not a closure".into());
        }
        if h.bloblet_head(closure).fields >= CLOSURE_FREE0 {
            return Err("a closure that captures".into());
        }
        let word = h.bloblet_slot(closure, CLOSURE_WORD);
        if let Some(p) = self.procs.get(&word.raw()) {
            return Ok(p.entry);
        }
        let rw = h.bloblet_slot(word, WORD_TWIN);
        if !h.is_register_word(rw) {
            return Err(format!("`{}` has no register code", self.name(word)));
        }
        let entry = self.a.label();
        self.procs.insert(word.raw(), Proc { entry });
        let arity = h.bloblet_slot(rw, WORD_CELL0 + 1).as_fixnum() as usize;
        self.order.push((word.raw(), self.name(word), arity));
        self.queue.push((word, rw));
        Ok(entry)
    }

    fn name(&self, word: Value) -> String {
        self.heap.symbol_name(self.heap.bloblet_slot(word, fixpt_heap::layout::cellular::WORD_NAME))
    }

    /// One procedure's code, from its register word `rw`.
    fn procedure(&mut self, word: Value, rw: Value) -> Result<(), String> {
        let h = self.heap;
        let fields = h.bloblet_head(rw).fields;
        let cells: Vec<Value> = (WORD_CELL0..=fields).map(|k| h.bloblet_slot(rw, k)).collect();
        let name = self.name(word);
        let decline = |what: String| Err(format!("`{name}`: {what}"));
        // Where each instruction starts, what a branch goes back to, and
        // whether the procedure has a frame or calls: what it must check.
        let mut starts = Vec::new();
        let mut back_to = vec![false; cells.len() + 1];
        let (mut frame, mut calls) = (None, false);
        let mut i = 0;
        while i < cells.len() {
            starts.push(i);
            let (op, n, _) = OPS[cells[i].as_fixnum() as usize];
            match op {
                "branch" | "branchf" => {
                    let to = i as i64 + 2 + cells[i + 1].as_fixnum();
                    if to <= i as i64 {
                        back_to[to as usize] = true;
                    }
                }
                "save" => frame = Some(cells[i + 1].as_fixnum() as usize),
                "invoke" | "tailinvoke" | "invokeself" => calls = true,
                _ => {}
            }
            i += 1 + n;
        }
        // Each call's callee, named by the global just before it (a tail
        // call's frame popped between).
        let op_at = |i: usize| OPS[cells[i].as_fixnum() as usize].0;
        let mut callees = HashMap::new();
        for (j, &i) in starts.iter().enumerate() {
            let call = starts[j + 1..].iter().copied().find(|&c| op_at(c) != "pop");
            if op_at(i) == "global" && let Some(c) = call.filter(|&c| matches!(op_at(c), "invoke" | "tailinvoke")) {
                let callee = h.bloblet_slot(cells[i + 1], 2);
                callees.insert(c, self.proc_of(callee).map_err(|e| format!("`{name}` calls {e}"))?);
            }
        }
        if frame.is_some_and(|m| 16 + 8 * m > 504) {
            return decline("a frame too large for one `stp`".into());
        }
        let entry = self.procs[&word.raw()].entry;
        let a = &mut self.a;
        let labels: Vec<Label> = (0..=cells.len()).map(|_| a.label()).collect();
        // Each trap site branches to a stub of its own, which calls the
        // trap's common code: so the return address says where it was.
        let mut stubs: Vec<(Label, u32)> = Vec::new();
        let mut trap = |a: &mut Asm, code: u32, c: Cond| {
            let l = a.label();
            stubs.push((l, code));
            a.to(l, Fix::If(c));
        };
        a.bind(entry);
        // Entered in the body's own terms: `invokeself` comes here too.
        let size = frame.map(|m| (16 + 8 * m as u32).div_ceil(16) * 16);
        if calls || frame.is_some() {
            a.e(subs_imm(FUEL, FUEL, 1));
            trap(a, OUT_OF_FUEL, Cond::Lo);
        }
        let mut pending_global: Option<Value> = None;
        for &i in &starts {
            a.bind(labels[i]);
            let (op, _, _) = OPS[cells[i].as_fixnum() as usize];
            let o = |j: usize| cells[i + 1 + j];
            let k = |v: Value| v.as_fixnum() as usize;
            let reg = |v: Value| v.as_fixnum() as Reg;
            if pending_global.is_some() && !matches!(op, "invoke" | "tailinvoke" | "pop") {
                return decline("a global read for its value".into());
            }
            match op {
                "args" => {}
                "const" => {
                    let v = o(0);
                    if !(v.is_fixnum() || v.raw() & 7 == 3) {
                        return decline("a constant in the heap".into());
                    }
                    a.es(&mov_imm64(RESULT, v.raw()));
                }
                "global" => pending_global = Some(o(0)),
                "reg" => a.e(mov(RESULT, reg(o(0)))),
                "setreg" => a.e(mov(reg(o(0)), RESULT)),
                "movereg" => a.e(mov(reg(o(1)), reg(o(0)))),
                // The frame: the caller's frame link and return address,
                // then the slots. The stack's limit is checked once it is
                // made; the limit leaves room for any one frame below it.
                "save" => {
                    a.e(stp_pre(FRAME, LINK, SP, -(size.expect("a frame") as i64)));
                    a.e(add_imm(FRAME, SP, 0));
                    a.e(ldr(X16, ST, st_off(offset_of!(DState, stack_limit))));
                    a.e(add_imm(X17, SP, 0));
                    a.e(cmp(X17, X16));
                    trap(a, STACK_OVERFLOW, Cond::Lo);
                }
                "pop" => a.e(ldp_post(FRAME, LINK, SP, size.expect("a frame") as i64)),
                "stack" => a.e(ldr(RESULT, FRAME, 16 + 8 * k(o(0)) as u32)),
                "setstk" => a.e(str(RESULT, FRAME, 16 + 8 * k(o(0)) as u32)),
                "load" => a.e(ldr(reg(o(0)), FRAME, 16 + 8 * k(o(1)) as u32)),
                "store" => a.e(str(reg(o(0)), FRAME, 16 + 8 * k(o(1)) as u32)),
                "op1" => match ROUTINES[k(o(0))].0 {
                    "pair-car" => a.e(ldur(RESULT, RESULT, -1)),
                    "pair-cdr" => a.e(ldur(RESULT, RESULT, 7)),
                    r => return decline(format!("op1 {r}")),
                },
                "op2" | "op2imm" => {
                    let other = if op == "op2" {
                        reg(o(1))
                    } else {
                        let v = o(1);
                        if !(v.is_fixnum() || v.raw() & 7 == 3) {
                            return decline("a constant in the heap".into());
                        }
                        a.es(&mov_imm64(X16, v.raw()));
                        X16
                    };
                    match ROUTINES[k(o(0))].0 {
                        "int-add" => {
                            a.e(adds(RESULT, RESULT, other));
                            trap(a, OVERFLOW, Cond::Vs);
                        }
                        "int-sub" => {
                            a.e(subs(RESULT, RESULT, other));
                            trap(a, OVERFLOW, Cond::Vs);
                        }
                        r @ ("int-less" | "eq") => {
                            a.e(cmp(RESULT, other));
                            a.es(&mov_imm64(X9, Value::TRUE.raw()));
                            a.es(&mov_imm64(X17, Value::FALSE.raw()));
                            a.e(csel(RESULT, X9, X17, if r == "eq" { Cond::Eq } else { Cond::Lt }));
                        }
                        r => return decline(format!("{op} {r}")),
                    }
                }
                "field" => a.e(ldur(RESULT, RESULT, -(4 + 8 * k(o(0)) as i64))),
                "invoke" | "tailinvoke" => {
                    if pending_global.take().is_none() {
                        return decline("a call of a procedure not named by a global".into());
                    }
                    let l = callees[&i];
                    if op == "invoke" { a.to(l, Fix::Bl) } else { a.to(l, Fix::B) }
                }
                "invokeself" => a.to(entry, Fix::Bl),
                "return" => a.e(ret()),
                "branch" | "branchf" => {
                    let to = (i as i64 + 2 + o(0).as_fixnum()) as usize;
                    if op == "branchf" {
                        a.es(&mov_imm64(X16, Value::FALSE.raw()));
                        a.e(cmp(RESULT, X16));
                        a.to(labels[to], Fix::If(Cond::Eq));
                    } else {
                        if back_to[to] {
                            a.e(subs_imm(FUEL, FUEL, 1));
                            trap(a, OUT_OF_FUEL, Cond::Lo);
                        }
                        a.to(labels[to], Fix::B);
                    }
                }
                other => return decline(format!("`{other}`")),
            }
        }
        a.bind(labels[cells.len()]);
        // The traps, out of the way: a stub per site, calling its kind's code.
        for (l, code) in &stubs {
            a.bind(*l);
            a.to(self.kinds[*code as usize], Fix::Bl);
        }
        Ok(())
    }
}
