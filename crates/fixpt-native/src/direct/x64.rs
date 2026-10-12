//! The native convention on x86_64: `direct.rs`'s trampoline, common
//! routines and compiler of procedures for the other instruction set, kept
//! as close to the arm64 ones as the two allow, step for step, so that a
//! change to one is easily made to the other. The Rust side (call-outs,
//! the stack cache, continuations, stack maps) is the same for both: the
//! frames are laid out alike.
//!
//! What x86_64 changes (CLAUDES_CHOICES.md, "The native convention on
//! x86_64"):
//!
//! | what                 | arm64           | x86_64                         |
//! | -------------------- | --------------- | ------------------------------ |
//! | `RESULT`             | `x0`            | `rax`                          |
//! | REG1…REG3            | `x1`–`x3`       | `rdi`, `rsi`, `r8`             |
//! | REG4…REG8            | `x4`–`x8`       | the state (`DState::regs`)     |
//! | the closure called   | `x10`           | `rbx`                          |
//! | the machine's state  | `x24`           | `r15`                          |
//! | frame link           | `x29`           | `rbp`                          |
//! | return address       | `x30`           | pushed by `call`; in the frame |
//! | fuel, the stack's limit, code's run address | `x28`, `x27`, `x26` | the state |
//! | scratch `X9`, `X11`–`X17` | the same   | `r10`, `r11`, `r12`, `rcx`, `rdx`, `r13`, `r9`, `r14` |
//!
//! The frame is the same: `[fp]` the link, `[fp + 8]` the return address,
//! `[fp + 16]` the stack map, the slots from `[fp + 24]`. A procedure with
//! a frame moves the return address its `call` pushed there (`save`), and
//! pushes it back when it pops its frame (`pop`), so that `ret` returns, or
//! a tail call's callee finds it where a `call` leaves it. A leaf keeps it
//! where the `call` left it. Every label a branch, a call or a `lea` names
//! is reached by a 32-bit displacement, so nothing is ever out of reach.
//! Raw `f64`s are operated on in `xmm0` and `xmm1`, as arm64's in `d16`
//! and `d17`; rounding is SSE4.1's `roundsd`.
//!
//! Where a REG in the state would meet a helper that uses every scratch
//! register (a blobref's element, write or variant), the primitive is
//! called instead.

use super::{
    overflow_info, Callout, Compiling, DState, Field, Proc, CONTROL_FRAME, MARK_MARK, NOT_A_PAIR, OUT_OF_FUEL, PRIM_FAILED, PROMPT_MARK, STACK_OVERFLOW,
    STACK_SLACK, TRAPS,
};
use super::reps::{self, Convert, Rep};
use crate::x86_64::*;
use fixpt_heap::layout::cellular::{CLOSURE_FREE0, CLOSURE_WORD, GLOBAL_WRITES, ROUTINES};
use fixpt_heap::layout::regcode::OPS;
use fixpt_heap::Value;
use std::collections::HashMap;
use std::mem::offset_of;

const RESULT: Reg = RAX;
/// The closure called, as the call enters it.
const CLO: Reg = RBX;
const ST: Reg = R15;
const FRAME: Reg = RBP;
const SP: Reg = RSP;
// Scratch, named for the arm64 registers they stand for.
const X9: Reg = R10;
const X11: Reg = R11;
const X12: Reg = R12;
const X13: Reg = RCX;
const X14: Reg = RDX;
const X15: Reg = R13;
const X16: Reg = R9;
const X17: Reg = R14;
/// The registers `RESULT` and REG1…REG3 live in (register code's `REG0`
/// is `RESULT` here, as on arm64, where it is `x0`).
const IN_REGS: [Reg; 4] = [RESULT, RDI, RSI, R8];

/// A field of the state, as an operand.
fn st(f: usize) -> Mem {
    m(ST, f as i32)
}

/// Field `k` of the bloblet whose `suffix + 4` is in `r`.
fn fld(r: Reg, k: usize) -> Mem {
    m(r, super::field_off(k) as i32)
}

/// Where `REGk` is (`RESULT` for 0): a register, or a word of the state.
#[derive(Copy, Clone, PartialEq)]
enum Loc {
    R(Reg),
    M(Mem),
}

fn loc(k: usize) -> Loc {
    match IN_REGS.get(k) {
        Some(&r) => Loc::R(r),
        None => Loc::M(st(offset_of!(DState, regs) + 8 * k)),
    }
}

/// `REGk`'s register, if it has one.
fn hw(k: usize) -> Option<Reg> {
    IN_REGS.get(k).copied()
}

#[derive(Copy, Clone)]
pub(super) struct Label(usize);

/// Instructions with labels, patched when everything is placed: every
/// reference to a label is the 32-bit displacement that ends its
/// instruction.
pub(super) struct Asm {
    code: Vec<u8>,
    labels: Vec<Option<usize>>,
    /// Each displacement to patch: where it is, and its label.
    fixups: Vec<(usize, usize)>,
    /// The last instruction, if it is a jump to a label: where it starts.
    last_jump: Option<usize>,
}

impl Asm {
    fn new() -> Asm {
        Asm { code: Vec::new(), labels: Vec::new(), fixups: Vec::new(), last_jump: None }
    }
    fn here(&self) -> usize {
        self.code.len()
    }
    fn e(&mut self, i: Ins) {
        self.code.extend_from_slice(&i);
        self.last_jump = None;
    }
    fn es(&mut self, bytes: &[u8]) {
        self.code.extend_from_slice(bytes);
        self.last_jump = None;
    }
    fn label(&mut self) -> Label {
        self.labels.push(None);
        Label(self.labels.len() - 1)
    }
    fn bind(&mut self, l: Label) {
        // A jump to here, just before it, goes.
        if let Some(at) = self.last_jump
            && self.fixups.last() == Some(&(at + 1, l.0))
        {
            self.fixups.pop();
            self.code.truncate(at);
        }
        self.last_jump = None;
        self.labels[l.0] = Some(self.here());
    }
    /// Whether a branch so far goes to `l`.
    fn used(&self, l: Label) -> bool {
        self.fixups.iter().any(|&(_, x)| x == l.0)
    }
    /// `i`, whose last four bytes are a displacement to `l`.
    fn to(&mut self, l: Label, i: Ins) {
        self.e(i);
        self.fixups.push((self.here() - 4, l.0));
    }
    fn jmp(&mut self, l: Label) {
        let at = self.here();
        self.to(l, jmp(0));
        self.last_jump = Some(at);
    }
    fn jcc(&mut self, c: Cond, l: Label) {
        self.to(l, jcc(c, 0));
    }
    fn call_l(&mut self, l: Label) {
        self.to(l, call(0));
    }
    /// `r` := where `l` is.
    fn lea_l(&mut self, r: Reg, l: Label) {
        self.to(l, lea_rip(r, 0));
    }
    /// `t` := field `k` of the code bloblet being made, by its distance:
    /// field `k` is `8k` bytes before the code's first.
    fn field(&mut self, t: Reg, k: usize) {
        let end = self.here() as i64 + 7;
        let i = load_rip(t, (-8 * k as i64 - end) as i32);
        debug_assert_eq!(i.len(), 7);
        self.e(i);
    }
    /// `r` := the constant `v`.
    fn imm(&mut self, r: Reg, v: u64) {
        self.e(mov_imm(r, v));
    }
    /// Compare `r` with the constant `v` (`X16` may be used for it).
    fn cmp_k(&mut self, r: Reg, v: u64) {
        match i32::try_from(v as i64) {
            Ok(k) => self.e(cmp_imm(r, k)),
            Err(_) => {
                self.imm(X16, v);
                self.e(cmp(r, X16));
            }
        }
    }
    /// `RESULT` := `#t` where `c` holds after the comparison just made,
    /// else `#f` (uses `t`).
    fn flag(&mut self, c: Cond, t: Reg) {
        self.imm(t, Value::TRUE.raw());
        self.imm(RESULT, Value::FALSE.raw());
        self.e(cmov(c, RESULT, t));
    }
    /// `REGk` in a register: its own, or `tmp`, loaded.
    fn get(&mut self, k: usize, tmp: Reg) -> Reg {
        match loc(k) {
            Loc::R(r) => r,
            Loc::M(mem) => {
                self.e(load(tmp, mem));
                tmp
            }
        }
    }
    /// `REGk` := `src`.
    fn put(&mut self, k: usize, src: Reg) {
        match loc(k) {
            Loc::R(r) if r == src => {}
            Loc::R(r) => self.e(mov(r, src)),
            Loc::M(mem) => self.e(store(mem, src)),
        }
    }
    /// `[mem]` := `REGk` (uses `tmp` for one in the state).
    fn store_reg(&mut self, mem: Mem, k: usize, tmp: Reg) {
        let r = self.get(k, tmp);
        self.e(store(mem, r));
    }
    /// `REGk` := `[mem]` (uses `tmp` for one in the state).
    fn load_reg(&mut self, k: usize, mem: Mem, tmp: Reg) {
        match loc(k) {
            Loc::R(r) => self.e(load(r, mem)),
            Loc::M(to) => {
                self.e(load(tmp, mem));
                self.e(store(to, tmp));
            }
        }
    }
    /// REG1…REG8 into the state's `args` (uses `X11`).
    fn regs_to_args(&mut self, n: usize) {
        let args = offset_of!(DState, args);
        for j in 0..n {
            self.store_reg(st(args + 8 * j), 1 + j, X11);
        }
    }
    fn finish(mut self) -> Result<Vec<u8>, String> {
        for (at, l) in std::mem::take(&mut self.fixups) {
            let to = self.labels[l].ok_or("a label never placed")?;
            // A jump to a `ret` is that `ret`: a fast path that joins the
            // slow one only to return.
            if self.code[at - 1] == 0xE9 && self.code[to] == 0xC3 {
                self.code[at - 1] = 0xC3;
                self.code[at..at + 4].fill(0xCC);
                continue;
            }
            let d = to as i64 - (at as i64 + 4);
            self.code[at..at + 4].copy_from_slice(&i32::try_from(d).map_err(|_| "code too long")?.to_le_bytes());
        }
        Ok(self.code)
    }
}

/// Whether this processor has SSE4.1 (`roundsd`).
fn sse41() -> bool {
    #[cfg(target_arch = "x86_64")]
    return std::is_x86_feature_detected!("sse4.1");
    #[cfg(not(target_arch = "x86_64"))]
    false
}

/// The machine stack pointer, as `rsp` names it (`SP` too: the native
/// stack is the machine's).
const RSP_: Reg = RSP;

/// From Rust, `entry(state, procedure)`, as `super::trampoline`: the
/// callee-saved registers saved, the native stack entered, the arguments
/// loaded, the procedure called, and back with its value. The common trap
/// leaves as it does, through the Rust stack pointer saved in the state.
pub(super) fn trampoline() -> Vec<u8> {
    let mut a = Asm::new();
    a.e(push(FRAME));
    a.e(mov(FRAME, RSP_));
    for r in [RBX, R12, R13, R14, R15] {
        a.e(push(r));
    }
    a.e(sub_imm(RSP_, 8));
    a.e(mov(ST, RDI));
    a.e(store(st(offset_of!(DState, rust_sp)), RSP_));
    a.e(load(CLO, st(offset_of!(DState, clo))));
    a.e(mov(X16, RSI));
    a.e(load(SP, st(offset_of!(DState, stack_top))));
    let args = offset_of!(DState, args);
    for k in 0..8 {
        a.load_reg(1 + k, st(args + 8 * k), X11);
    }
    // The count, for a variadic procedure (`vargs`).
    a.e(load(X9, st(offset_of!(DState, nargs))));
    // What the outermost frame links and returns to, for the stack cache
    // to give a frame it restores last.
    let back = a.label();
    a.e(store(st(offset_of!(DState, bottom_link)), FRAME));
    a.lea_l(X17, back);
    a.e(store(st(offset_of!(DState, bottom_ret)), X17));
    a.e(call_r(X16));
    a.bind(back);
    leave(&mut a);
    a.finish().expect("labels bound")
}

/// Back to Rust from anywhere on the native stack.
fn leave(a: &mut Asm) {
    a.e(load(RSP_, st(offset_of!(DState, rust_sp))));
    a.e(add_imm(RSP_, 8));
    for r in [R15, R14, R13, R12, RBX] {
        a.e(pop(r));
    }
    a.e(pop(FRAME));
    a.e(ret());
}

/// Where a call-out that does not return to its caller said to go: its
/// stack, frame and value, and there.
fn resume(a: &mut Asm) {
    a.e(load(SP, st(offset_of!(DState, resume_sp))));
    a.e(load(FRAME, st(offset_of!(DState, resume_fp))));
    a.e(load(RESULT, st(offset_of!(DState, resume_x0))));
    a.e(jmp_m(st(offset_of!(DState, resume_pc))));
}

/// Call-out `n`, its arguments in the state already: on Rust's stack,
/// with where the native frames are for its collections to find.
fn call_out(a: &mut Asm, n: usize) {
    a.e(store(st(offset_of!(DState, fp)), FRAME));
    a.e(store(st(offset_of!(DState, native_sp)), SP));
    a.e(load(RSP_, st(offset_of!(DState, rust_sp))));
    a.e(mov(RDI, ST));
    a.imm(RSI, n as u64);
    a.e(call_m(st(offset_of!(DState, callout))));
    // The stack and frame as the call-out left them: a collection flushes
    // the frames into the heap and restores the innermost elsewhere.
    a.e(load(SP, st(offset_of!(DState, native_sp))));
    a.e(load(FRAME, st(offset_of!(DState, fp))));
}

/// The state's trap tested after a call-out: to `failed` if one was set.
fn trapped(a: &mut Asm, failed: Label) {
    a.e(alu_mi(Alu::Cmp, st(offset_of!(DState, trap)), 0));
    a.jcc(Cond::Ne, failed);
}

/// The common trap's way from code with no stub of its own: the kind in
/// `X9`, where it was the return address a `call` of the next instruction
/// pushes.
fn fail_here(a: &mut Asm, code: u32) {
    let stub = a.label();
    a.call_l(stub);
    a.bind(stub);
    a.imm(X9, code as u64);
    a.e(jmp_m(st(offset_of!(DState, trap_stub))));
}

/// `RESULT` and REG1…REG8 into the state's `kept`, or back.
fn keep(a: &mut Asm, n: usize, back: bool) {
    let kept = offset_of!(DState, kept);
    for r in 0..n {
        if back {
            a.load_reg(r, st(kept + 8 * r), X11);
        } else {
            a.store_reg(st(kept + 8 * r), r, X11);
        }
    }
}

/// The stack cache's underflow: where the last frame on the cache returns,
/// its value in `RESULT` (REG1…REG8 kept too), as `super::common_underflow`.
pub(super) fn common_underflow(n: usize) -> Vec<u8> {
    let mut a = Asm::new();
    keep(&mut a, 9, false);
    call_out(&mut a, n);
    let failed = a.label();
    trapped(&mut a, failed);
    keep(&mut a, 9, true);
    a.e(load(SP, st(offset_of!(DState, resume_sp))));
    a.e(load(FRAME, st(offset_of!(DState, resume_fp))));
    a.e(jmp_m(st(offset_of!(DState, resume_pc))));
    a.bind(failed);
    a.imm(X9, PRIM_FAILED as u64);
    a.e(jmp_m(st(offset_of!(DState, trap_stub))));
    a.finish().expect("labels bound")
}

/// The stack cache's overflow, as `super::common_overflow`: from a
/// procedure's entry whose frame, just made, passed the cache's limit, by
/// a `call` from the site's stub, its code bloblet in `X16`, which of its
/// registers hold values in `X17`. The return address is kept where
/// arm64's link is (`kept[11]`), and returned to by pushing it again.
pub(super) fn common_overflow(n: usize) -> Vec<u8> {
    let mut a = Asm::new();
    let kept = offset_of!(DState, kept);
    a.e(pop(X11));
    a.e(store(st(kept + 88), X11));
    keep(&mut a, 9, false);
    a.e(store(st(kept + 72), X9));
    a.e(store(st(kept + 80), CLO));
    a.e(store(st(offset_of!(DState, overflow_code)), X16));
    a.e(store(st(offset_of!(DState, overflow_info)), X17));
    call_out(&mut a, n);
    let failed = a.label();
    trapped(&mut a, failed);
    a.e(load(SP, st(offset_of!(DState, resume_sp))));
    a.e(load(FRAME, st(offset_of!(DState, resume_fp))));
    keep(&mut a, 9, true);
    a.e(load(X9, st(kept + 72)));
    a.e(load(CLO, st(kept + 80)));
    a.e(push_m(st(kept + 88)));
    a.e(ret());
    a.bind(failed);
    a.imm(X9, PRIM_FAILED as u64);
    a.e(jmp_m(st(offset_of!(DState, trap_stub))));
    a.finish().expect("labels bound")
}

/// The common trap: the kind (in `X9`) recorded, and where (the return
/// address, one past its site's stub, a `call`), then back to Rust.
pub(super) fn common_trap() -> Vec<u8> {
    let mut a = Asm::new();
    a.e(store(st(offset_of!(DState, trap)), X9));
    a.e(pop(X9));
    a.e(sub_imm(X9, 5));
    a.e(store(st(offset_of!(DState, pc)), X9));
    leave(&mut a);
    a.finish().expect("no labels")
}

/// A frame of its own, with nothing in it, under the return address a
/// `call` (or, in a tail call, the caller's) left: the link below it.
fn small_frame(a: &mut Asm) {
    a.e(sub_imm(SP, 8));
    a.e(store(m(SP, 0), FRAME));
    a.e(mov(FRAME, SP));
}

/// That frame left, and back.
fn small_return(a: &mut Asm) {
    a.e(load(FRAME, m(SP, 0)));
    a.e(add_imm(SP, 8));
    a.e(ret());
}

/// The common call of what is not native code, as `super::common_foreign`:
/// the arguments' count in `X9`, the callee in `CLO`, from a `call` or, in
/// a tail call, a `jmp` (the return address on the stack either way).
pub(super) fn common_foreign(n: usize) -> Vec<u8> {
    let mut a = Asm::new();
    small_frame(&mut a);
    a.e(store(st(offset_of!(DState, nargs)), X9));
    a.e(store(st(offset_of!(DState, aux)), CLO));
    a.regs_to_args(8);
    call_out(&mut a, n);
    let (failed, resumed) = (a.label(), a.label());
    trapped(&mut a, failed);
    // Back with an abort to a prompt in these frames: resumed there.
    a.e(alu_mi(Alu::Cmp, st(offset_of!(DState, foreign_resume)), 0));
    a.jcc(Cond::Ne, resumed);
    small_return(&mut a);
    a.bind(resumed);
    a.e(store_imm(st(offset_of!(DState, foreign_resume)), 0));
    resume(&mut a);
    a.bind(failed);
    fail_here(&mut a, PRIM_FAILED);
    a.finish().expect("labels bound")
}

/// The common making of a closure by call-out, as `super::common_closure`:
/// the count of free values (in REG1…REGn) in `X9`, the code in `X17`.
pub(super) fn common_closure(n: usize) -> Vec<u8> {
    let mut a = Asm::new();
    small_frame(&mut a);
    a.e(store(st(offset_of!(DState, nargs)), X9));
    a.e(store(st(offset_of!(DState, aux)), X17));
    a.regs_to_args(8);
    call_out(&mut a, n);
    let failed = a.label();
    trapped(&mut a, failed);
    small_return(&mut a);
    a.bind(failed);
    fail_here(&mut a, PRIM_FAILED);
    a.finish().expect("labels bound")
}

/// Where a thunk a mark in tail position called returns: its mark's frame
/// popped, and back to that frame's return address.
pub(super) fn mark_ret() -> Vec<u8> {
    let mut a = Asm::new();
    a.e(load(X11, m(SP, 8)));
    a.e(load(FRAME, m(SP, 0)));
    a.e(add_imm(SP, CONTROL_FRAME as i32));
    a.e(jmp_r(X11));
    a.finish().expect("no labels")
}

/// `super::adapt`'s code: the closure called now `f`, its free value 0,
/// called as what is not native code, in a tail call.
pub(super) fn adapter() -> Vec<u8> {
    let mut a = Asm::new();
    a.e(load(CLO, fld(CLO, CLOSURE_FREE0)));
    a.e(jmp_m(st(offset_of!(DState, foreign))));
    a.finish().expect("no labels")
}

/// `common_poll`, `common_cons` and `common_bloblet`: not yet ported to
/// x86_64 (the native convention is off there until it is re-ported onto
/// the frames of `TODO.md` §91); a trap if reached.
pub(super) fn common_poll() -> Vec<u8> {
    vec![0x0f, 0x0b]
}
pub(super) fn common_cons() -> Vec<u8> {
    vec![0x0f, 0x0b]
}
pub(super) fn common_bloblet() -> Vec<u8> {
    vec![0x0f, 0x0b]
}

impl Compiling<'_> {
    /// The continuation procedure, as `resume_proc`: given the value (in
    /// REG1), the closure in `CLO`, in a frame of its own it calls out to
    /// put the continuation's frames back, and goes where they resume.
    pub(super) fn resume_proc_x64(&mut self) -> usize {
        let mut a = Asm::new();
        small_frame(&mut a);
        let args = offset_of!(DState, args);
        a.store_reg(st(args), 1, X11);
        a.e(store(st(args + 8), CLO));
        let n = self.callouts.len();
        self.callouts.push(Callout::Reinstate);
        call_out(&mut a, n);
        let failed = a.label();
        trapped(&mut a, failed);
        resume(&mut a);
        a.bind(failed);
        leave(&mut a);
        let code = a.finish().expect("placed");
        let q = self.procs.len();
        self.procs.push(Proc { word: Value::FALSE, rw: Value::FALSE, name: "continuation".into(), arity: 1, fields: vec![Field::Myself, Field::Const(Value::FALSE)], len: code.len(), code, global: false, params: Some(0) });
        self.resume = Some(q);
        q
    }

    /// One procedure's code, from its register word, as `procedure`.
    pub(super) fn procedure_x64(&mut self, p: usize) -> Result<(), String> {
        let h = self.heap;
        let (word, rw) = (self.procs[p].word, self.procs[p].rw);
        let fields = h.bloblet_head(rw).fields;
        let cells: Vec<Value> = (fixpt_heap::layout::cellular::WORD_CELL0..=fields).map(|k| h.bloblet_slot(rw, k)).collect();
        let name = self.name(word);
        let decline = |what: String| Err(format!("`{name}`: {what}"));
        // Where each instruction starts, what a branch goes back to, and
        // whether the procedure has a frame, calls, or reads its closure.
        let mut starts = Vec::new();
        let mut back_to = vec![false; cells.len() + 1];
        let mut target = vec![false; cells.len() + 1];
        let (mut frame, mut calls, mut captures) = (None, false, false);
        let mut i = 0;
        while i < cells.len() {
            starts.push(i);
            let (op, n, _) = OPS[cells[i].as_fixnum() as usize];
            match op {
                "branch" | "branchf" | "brancht" | "global-guard" => {
                    let to = i as i64 + 1 + n as i64 + cells[i + n].as_fixnum();
                    target[to as usize] = true;
                    if to <= i as i64 {
                        back_to[to as usize] = true;
                    }
                }
                "save" => frame = Some(cells[i + 1].as_fixnum() as usize),
                "invoke" | "tailinvoke" | "invokeself" => calls = true,
                "lexical" => captures = true,
                _ => {}
            }
            i += 1 + n;
        }
        let op_at = |j: usize| OPS[cells[j].as_fixnum() as usize].0;
        // Whether this procedure's frame is pushed where each instruction
        // starts: after `save`, pushed; after `pop`, not; where a branch
        // goes, as at the branch.
        let mut framed = vec![false; cells.len() + 1];
        {
            let mut known: Vec<Option<bool>> = vec![None; cells.len() + 1];
            let mut cur = false;
            for &i in &starts {
                if let Some(k) = known[i] {
                    cur = k;
                }
                framed[i] = cur;
                let (op, n, _) = OPS[cells[i].as_fixnum() as usize];
                match op {
                    "save" => cur = true,
                    "pop" => cur = false,
                    "branch" | "branchf" | "brancht" | "global-guard" => {
                        let to = (i as i64 + 1 + n as i64 + cells[i + n].as_fixnum()) as usize;
                        known[to].get_or_insert(cur);
                    }
                    _ => {}
                }
            }
        }
        // What each `global` is for: a call just after it (a tail call's
        // frame popped between), or its value.
        let called = |j: usize| {
            let at = starts.iter().position(|&s| s == j).expect("an instruction");
            starts[at + 1..].iter().copied().find(|&c| op_at(c) != "pop").filter(|&c| matches!(op_at(c), "invoke" | "tailinvoke"))
        };
        if frame.is_some_and(|m| 24 + 8 * (m + 2) > 4080) {
            return decline("a frame too large".into());
        }
        let unmapped = frame.is_some_and(|m| m + 2 > 60);
        let size = frame.map(|m| (24 + 8 * (m as u32 + 2)).div_ceil(16) as i32 * 16);
        let self_slot = frame.map(|m| 24 + 8 * m as i32);
        let clo_slot = frame.map(|m| 24 + 8 * (m as i32 + 1));
        // Which slots are live after each instruction (`procedure`'s pass).
        let live_out = {
            let at_of: HashMap<usize, usize> = starts.iter().enumerate().map(|(si, &i)| (i, si)).collect();
            let ns = starts.len();
            let (mut uses, mut defs) = (vec![0u64; ns], vec![0u64; ns]);
            let mut succ: Vec<Vec<usize>> = vec![Vec::new(); ns];
            for (si, &i) in starts.iter().enumerate() {
                let (op, n, _) = OPS[cells[i].as_fixnum() as usize];
                let bit = |j: usize| 1u64.checked_shl(cells[i + 1 + j].as_fixnum() as u32).unwrap_or(0);
                match op {
                    "stack" => uses[si] |= bit(0),
                    "load" => uses[si] |= bit(1),
                    "setstk" => defs[si] |= bit(0),
                    "store" => defs[si] |= bit(1),
                    _ => {}
                }
                let to = || at_of[&((i as i64 + 1 + n as i64 + cells[i + n].as_fixnum()) as usize)];
                match op {
                    "return" | "tailinvoke" => {}
                    "branch" => succ[si].push(to()),
                    "branchf" | "brancht" | "global-guard" => succ[si].extend([si + 1, to()]),
                    _ if si + 1 < ns => succ[si].push(si + 1),
                    _ => {}
                }
            }
            let (mut live_in, mut live_out) = (vec![0u64; ns], vec![0u64; ns]);
            loop {
                let mut changed = false;
                for si in (0..ns).rev() {
                    let out = succ[si].iter().fold(0, |m, &t| m | live_in[t]);
                    let inn = (out & !defs[si]) | uses[si];
                    if (out, inn) != (live_out[si], live_in[si]) {
                        (live_out[si], live_in[si], changed) = (out, inn, true);
                    }
                }
                if !changed {
                    break live_out;
                }
            }
        };
        let prim_name = |p: usize| fixpt_runtime::PRIMITIVES.get(p).map_or("?", |d| d.name);
        let raw_refs = reps::raw_refs(&cells, &starts, &prim_name, &[]);
        let mut map_stored: Option<u64>;
        let mut a = Asm::new();
        let entry = a.label();
        let labels: Vec<Label> = (0..=cells.len()).map(|_| a.label()).collect();
        let mut stubs: Vec<(Label, u32)> = Vec::new();
        let mut foreign: Vec<(Label, Label, usize, bool)> = Vec::new();
        let mut overflows: Vec<(Label, Label)> = Vec::new();
        let mut cell_slows: Vec<(Label, Label, Label)> = Vec::new();
        let (resume_at, mut uses_resume) = (a.label(), false);
        let trap = |a: &mut Asm, stubs: &mut Vec<(Label, u32)>, code: u32, c: Cond| {
            let l = a.label();
            stubs.push((l, code));
            a.jcc(c, l);
        };
        let fuel = |a: &mut Asm, stubs: &mut Vec<(Label, u32)>| {
            a.e(alu_mi(Alu::Sub, st(offset_of!(DState, fuel)), 1));
            trap(a, stubs, OUT_OF_FUEL, Cond::B);
        };
        a.bind(entry);
        if calls || frame.is_some() {
            fuel(&mut a, &mut stubs);
        }
        let sets_first = |j: usize| matches!(op_at(j), "const" | "reg" | "stack" | "global" | "lexical");
        let ignores = |j: usize| sets_first(j) || matches!(op_at(j), "invokeself");
        let joinable = |si: usize| starts.get(si + 1).copied().filter(|&j| !target[j]);
        let si_at: HashMap<usize, usize> = starts.iter().enumerate().map(|(si, &i)| (i, si)).collect();
        let has_int = starts.iter().any(|&i| matches!(op_at(i), "op2" | "op2imm") && reps::int_routine(cells[i + 1].as_fixnum() as usize));
        let live = reps::live_in(&cells, &starts, &prim_name, &[]);
        let labels_g = labels;
        let labels_f: Vec<Label> = (0..=cells.len()).map(|_| a.label()).collect();
        let versions: &[bool] = if has_int { &[true, false] } else { &[false] };
        let mut edge_stubs: Vec<(Label, Vec<(usize, Rep)>, Vec<usize>, Label, Label)> = Vec::new();
        let mut int_slows: Vec<IntSlow> = Vec::new();
        for &fast in versions {
        let labels = if fast { &labels_f } else { &labels_g };
        let (reps_in, reps_out) = reps::reps_of(&cells, &starts, &prim_name, fast, &[], 0, &vec![0; starts.len()]);
        let mut src = RESULT;
        let mut pending: Option<Field> = None;
        let mut bound: Option<(Value, Value)> = None;
        map_stored = None;
        let mut edge = |a: &mut Asm, from: usize, to: usize| -> Label {
            let (unbox, check) = match si_at.get(&to) {
                Some(&t) => (
                    reps::unboxes(&reps_out[from], &reps_in[t]),
                    if fast { reps::checks(&reps_out[from], &reps_in[t], &live[t]) } else { vec![] },
                ),
                None => (vec![], vec![]),
            };
            if unbox.is_empty() && check.is_empty() {
                return labels[to];
            }
            let l = a.label();
            edge_stubs.push((l, unbox, check, labels[to], labels_g[to]));
            l
        };
        let mut si = 0;
        while si < starts.len() {
            let i = starts[si];
            // Falling in from the instruction before, the registers it
            // leaves as values that are raw here unboxed; in the fixnum
            // version, those it leaves unknown that are known here tested.
            if si > 0 && !matches!(op_at(starts[si - 1]), "branch" | "return" | "tailinvoke") {
                for (r, rep) in reps::unboxes(&reps_out[si - 1], &reps_in[si]) {
                    unbox_to(&mut a, self.callouts, r, rep);
                }
                if fast {
                    for r in reps::checks(&reps_out[si - 1], &reps_in[si], &live[si]) {
                        check_fixnum(&mut a, r, labels_g[i]);
                    }
                }
            }
            si += 1;
            a.bind(labels[i]);
            let op = op_at(i);
            {
                let o = |j: usize| cells[i + 1 + j];
                let mut reps = reps_in[si - 1];
                let first = reps::step(op, &o, &prim_name, raw_refs[si - 1], fast, &[], reps::Calls { own: 0, callee: 0 }, &mut reps);
                // `RESULT`, where a `reg` just before left it in its register
                // (`src`), is tested there.
                convert(&mut a, self.callouts, &first, labels_g[i], src);
            }
            if target[i] {
                map_stored = None;
            }
            // Before what may collect, in a frame: the slots live after it,
            // the code bloblet's, and the closure's if the code reads it.
            if let Some(fm) = frame
                && framed[i]
                && matches!(op, "prim" | "cellular" | "lambda" | "invokeself" | "invoke")
            {
                let map = if unmapped { u64::MAX } else { live_out[si - 1] | 1 << fm | if captures { 1 << (fm + 1) } else { 0 } };
                if map_stored != Some(map) {
                    a.imm(X16, Value::fixnum(if unmapped { -1 } else { map as i64 }).raw());
                    a.e(store(m(FRAME, 16), X16));
                    map_stored = Some(map);
                }
            }
            let o = |j: usize| cells[i + 1 + j];
            let k = |v: Value| v.as_fixnum() as usize;
            match op {
                "args" => {}
                // Entered with any number of arguments, their count in X9:
                // it and the registers into the state, for `rest` to list.
                "vargs" => {
                    a.e(store(st(offset_of!(DState, nargs)), X9));
                    a.regs_to_args(8);
                }
                "const" => {
                    let v = o(0);
                    if v.is_fixnum() || v.raw() & 7 == 3 {
                        a.imm(RESULT, v.raw());
                    } else if h.is_cellular_word(v) {
                        let q = self.proc_of(v).map_err(|e| format!("`{name}` makes a closure of {e}"))?;
                        let f = self.field(p, Field::Code(q));
                        a.field(RESULT, f);
                    } else if let Some((word, free)) = self.closure_parts(v)
                        && free.is_empty()
                        && self.name(word) != "undefined"
                    {
                        let q = self.proc_of(word).map_err(|e| format!("`{name}` calls {e}"))?;
                        if called(i).is_some() {
                            pending = Some(Field::Code(q));
                        } else {
                            let f = self.field(p, Field::Closure(q, vec![]));
                            a.field(RESULT, f);
                        }
                    } else {
                        let f = self.field(p, Field::Const(v));
                        a.field(RESULT, f);
                    }
                }
                "global" => {
                    let cell = o(0);
                    let writes = self.heap.bloblet_slot(cell, GLOBAL_WRITES);
                    let g = self.global_value(cell).map_err(|e| format!("`{name}` calls {e}"))?;
                    if called(i).is_some() {
                        if !matches!(g, Field::Cell(_)) {
                            bound = Some((cell, writes));
                        }
                        pending = Some(g);
                    } else {
                        let fc = self.field(p, Field::Cell(cell));
                        a.field(X9, fc);
                        a.e(load(RESULT, fld(X9, 2)));
                        if !matches!(g, Field::Cell(_)) {
                            let other = a.label();
                            a.e(load(X11, fld(X9, GLOBAL_WRITES)));
                            a.imm(X16, writes.raw());
                            a.e(cmp(X11, X16));
                            a.jcc(Cond::Ne, other);
                            let f = match g {
                                Field::Code(q) => self.field(p, Field::Closure(q, vec![])),
                                g => self.field(p, g),
                            };
                            a.field(RESULT, f);
                            a.bind(other);
                        }
                    }
                }
                "global-guard" => {
                    let (cell, n, to) = (o(0), o(1), (i as i64 + 4 + o(2).as_fixnum()) as usize);
                    let fc = self.field(p, Field::Cell(cell));
                    a.field(X9, fc);
                    a.e(load(X11, fld(X9, GLOBAL_WRITES)));
                    a.imm(X16, n.raw());
                    a.e(cmp(X11, X16));
                    let l = edge(&mut a, si - 1, to);
                    a.jcc(Cond::Ne, l);
                }
                "setglbl" => {
                    let f = self.field(p, Field::Cell(o(0)));
                    a.field(X9, f);
                    a.e(store(fld(X9, 2), RESULT));
                    // One more write, for the guards (`global-guard`).
                    a.e(alu_mi(Alu::Add, fld(X9, GLOBAL_WRITES), Value::fixnum(1).raw() as i32));
                    a.es(&card_mark(X9, fld(X9, 2).disp, ST, offset_of!(DState, cards) as i32, X16, X17));
                }
                "lexical" => {
                    let from = match clo_slot.filter(|_| framed[i]) {
                        Some(s) => {
                            a.e(load(X9, m(FRAME, s)));
                            X9
                        }
                        None => CLO,
                    };
                    let off = super::field_off(CLOSURE_FREE0 + k(o(0)));
                    if off < -256 {
                        return decline("a closure too large".into());
                    }
                    a.e(load(RESULT, m(from, off as i32)));
                }
                "reg" => match (joinable(si - 1), hw(k(o(0)))) {
                    (Some(j), Some(r)) if matches!(op_at(j), "op2" | "op2imm") && !matches!(reps_in[si - 1][k(o(0)).min(8)], Rep::Raw { .. }) => {
                        src = r;
                        continue;
                    }
                    _ => {
                        let r = a.get(k(o(0)), RESULT);
                        if r != RESULT {
                            a.e(mov(RESULT, r));
                        }
                    }
                },
                "setreg" => a.put(k(o(0)), RESULT),
                "movereg" => {
                    let r = a.get(k(o(0)), X16);
                    a.put(k(o(1)), r);
                }
                // The frame made, as `procedure` makes it, the return
                // address `call` pushed (now the frame's top word) moved to
                // its second.
                "save" => {
                    let size = size.expect("a frame");
                    a.e(sub_imm(SP, size - 8));
                    a.e(load(X11, m(SP, size - 8)));
                    a.e(store(m(SP, 8), X11));
                    a.e(store(m(SP, 0), FRAME));
                    a.e(mov(FRAME, SP));
                    // Past the stack cache's limit: the rest flushed into
                    // the heap, and this frame moved to the cache's top.
                    a.e(alu_rm(Alu::Cmp, SP, st(offset_of!(DState, stack_limit))));
                    let (over, back) = (a.label(), a.label());
                    a.jcc(Cond::B, over);
                    a.bind(back);
                    overflows.push((over, back));
                    map_stored = None;
                    if unmapped {
                        for off in (24..size).step_by(8) {
                            a.e(store_imm(m(FRAME, off), 0));
                        }
                    } else {
                        let unwritten = live_out[si - 1];
                        for k in (0..64).filter(|k| unwritten & (1 << k) != 0) {
                            a.e(store_imm(m(FRAME, 24 + 8 * k), 0));
                        }
                    }
                    a.field(X9, 1);
                    a.e(store(m(FRAME, self_slot.expect("a frame")), X9));
                    if captures {
                        a.e(store(m(FRAME, clo_slot.expect("a frame")), CLO));
                    }
                }
                // The frame popped, its return address pushed again.
                "pop" => {
                    let size = size.expect("a frame");
                    a.e(load(X11, m(SP, 8)));
                    a.e(load(FRAME, m(SP, 0)));
                    a.e(add_imm(SP, size));
                    a.e(push(X11));
                }
                "stack" => a.e(load(RESULT, m(FRAME, 24 + 8 * k(o(0)) as i32))),
                "setstk" => a.e(store(m(FRAME, 24 + 8 * k(o(0)) as i32), RESULT)),
                "load" => a.load_reg(k(o(0)), m(FRAME, 24 + 8 * k(o(1)) as i32), X11),
                "store" => {
                    a.store_reg(m(FRAME, 24 + 8 * k(o(1)) as i32), k(o(0)), X11);
                    // Its slot read back at once: the register is still it.
                    if let Some(j) = joinable(si - 1)
                        && op_at(j) == "stack"
                        && cells[j + 1] == o(1)
                    {
                        a.bind(labels[j]);
                        si += 1;
                        match (joinable(si - 1), hw(k(o(0)))) {
                            (Some(n), Some(r)) if matches!(op_at(n), "op2" | "op2imm") => src = r,
                            _ => {
                                let r = a.get(k(o(0)), RESULT);
                                if r != RESULT {
                                    a.e(mov(RESULT, r));
                                }
                            }
                        }
                    }
                }
                "op1" => match ROUTINES[k(o(0))].0 {
                    // A list may be `nil`: `car` of it traps.
                    r @ ("pair-car" | "pair-cdr") => {
                        a.e(mov(X16, RESULT));
                        a.e(and_imm(X16, 7));
                        a.e(cmp_imm(X16, fixpt_heap::value::TAG_PAIR as i32));
                        trap(&mut a, &mut stubs, NOT_A_PAIR, Cond::Ne);
                        a.e(load(RESULT, m(RESULT, if r == "pair-car" { -1 } else { 7 })));
                    }
                    r => return decline(format!("op1 {r}")),
                },
                "op2" | "op2imm" => {
                    let x = std::mem::replace(&mut src, RESULT);
                    // The other operand: a register, or a constant, which an
                    // add, a subtract or a compare may take as it is.
                    let (other, small) = if op == "op2" {
                        (a.get(k(o(1)), X16), None)
                    } else {
                        let v = o(1);
                        if !(v.is_fixnum() || v.raw() & 7 == 3) {
                            let f = self.field(p, Field::Const(v));
                            a.field(X16, f);
                            (X16, None)
                        } else if let Ok(n) = i32::try_from(v.raw() as i64) {
                            (X16, Some(n))
                        } else {
                            a.imm(X16, v.raw());
                            (X16, None)
                        }
                    };
                    let r = ROUTINES[k(o(0))].0;
                    let fast_int = fast && reps::int_routine(k(o(0)));
                    // A sum or difference only moved on to a register, and
                    // then not read: made in that register, if it has one.
                    let mut d = RESULT;
                    if matches!(r, "int-add" | "int-sub")
                        && let Some(j) = joinable(si - 1)
                        && op_at(j) == "setreg"
                        && let Some(dr) = hw(k(cells[j + 1]))
                        && starts.get(si + 1).is_some_and(|&f| ignores(f))
                    {
                        a.bind(labels[j]);
                        d = dr;
                        si += 1;
                    }
                    let prim = match r {
                        "int-add" => Some("%fx26-add"),
                        "int-sub" => Some("%fx26-sub"),
                        "int-less" => Some("%fx26-int-less"),
                        "int-eq" => Some("%fx26-int-eq"),
                        "eq" => None,
                        _ => return decline(format!("{op} {r}")),
                    }
                    .map(|n| fixpt_runtime::PRIMITIVES.iter().position(|d| d.name == n).expect("a primitive"))
                    .filter(|_| !fast_int && !(r == "int-eq" && op == "op2imm" && o(1).is_fixnum()));
                    let (entry, back) = (a.label(), a.label());
                    let mut slow = IntSlow { entry, overflow: None, back, x, y: other, imm: small, into: d, prim: 0, sub: r == "int-sub", branch: None };
                    if prim.is_some() {
                        if small.is_some() || other == x {
                            a.e(test_imm(x, 7));
                        } else {
                            a.e(mov(X13, x));
                            a.e(or(X13, other));
                            a.e(test_imm(X13, 7));
                        }
                        a.jcc(Cond::Ne, entry);
                    }
                    let dst = if (small.is_none() && d == other) || (fast_int && d == x) { X13 } else { d };
                    let two = |a: &mut Asm, op: Alu| {
                        if dst != x {
                            a.e(mov(dst, x));
                        }
                        match small {
                            Some(n) => a.e(alu_imm(op, dst, n)),
                            None => a.e(alu(op, dst, other)),
                        }
                    };
                    match (r, small) {
                        ("int-add", _) => two(&mut a, Alu::Add),
                        ("int-sub", _) => two(&mut a, Alu::Sub),
                        (_, Some(n)) => a.e(cmp_imm(x, n)),
                        (_, None) => a.e(cmp(x, other)),
                    }
                    let cond = if r == "int-less" { Cond::L } else { Cond::E };
                    match r {
                        "int-add" | "int-sub" if fast_int => {
                            a.jcc(Cond::O, labels_g[i]);
                            if dst != d {
                                a.e(mov(d, dst));
                            }
                        }
                        "int-add" | "int-sub" => {
                            let ov = a.label();
                            a.jcc(Cond::O, ov);
                            if dst != d {
                                a.e(mov(d, dst));
                            }
                            slow.overflow = Some(ov);
                        }
                        // A test that only a branch reads: the branch on the
                        // flags, with no boolean made.
                        _ => match joinable(si - 1) {
                            Some(j)
                                if matches!(op_at(j), "branchf" | "brancht")
                                    && starts.get(si + 1).is_none_or(|&f| sets_first(f))
                                    && sets_first((j as i64 + 2 + cells[j + 1].as_fixnum()) as usize) =>
                            {
                                a.bind(labels[j]);
                                let to = (j as i64 + 2 + cells[j + 1].as_fixnum()) as usize;
                                let taken_if_true = op_at(j) == "brancht";
                                let cond = match (taken_if_true, cond) {
                                    (false, Cond::E) => Cond::Ne,
                                    (false, _) => Cond::Ge,
                                    (true, c) => c,
                                };
                                let l = edge(&mut a, si, to);
                                a.jcc(cond, l);
                                slow.branch = Some((l, taken_if_true));
                                slow.into = RESULT;
                                si += 1;
                            }
                            _ => {
                                a.flag(cond, X9);
                                slow.into = RESULT;
                            }
                        },
                    }
                    if let Some(p) = prim {
                        slow.prim = p;
                        int_slows.push(slow);
                    }
                    a.bind(back);
                }
                "field" => {
                    let off = super::field_off(k(o(0)));
                    if off < -256 {
                        return decline("a field too far".into());
                    }
                    a.e(load(RESULT, m(RESULT, off as i32)));
                }
                "setfield" => {
                    let off = super::field_off(k(o(0)));
                    if off < -256 {
                        return decline("a field too far".into());
                    }
                    a.store_reg(m(RESULT, off as i32), k(o(1)), X11);
                    a.es(&card_mark(RESULT, off as i32, ST, offset_of!(DState, cards) as i32, X16, X17));
                }
                // Control, on the native stack, as `procedure` does it.
                "cellular" if matches!(ROUTINES.get(k(o(0))).map(|r| r.0), Some("prompt" | "withmark" | "withmark-tail" | "abort" | "callcc" | "callcomp" | "firstmark" | "currentmarks" | "marksof")) => {
                    if frame.is_none() {
                        return decline("a call-out outside a frame".into());
                    }
                    let args = offset_of!(DState, args);
                    // A call of the closure in `CLO`, `n` arguments in
                    // registers, back at `after`: native code, or not.
                    let call_clo = |a: &mut Asm, foreign: &mut Vec<(Label, Label, usize, bool)>, n: usize, after: Label| {
                        let stub = a.label();
                        a.e(load(X16, fld(CLO, CLOSURE_WORD)));
                        a.e(alu_rm(Alu::Cmp, X16, st(offset_of!(DState, code_lo))));
                        a.jcc(Cond::B, stub);
                        foreign.push((stub, after, n, false));
                        a.e(alu_rm(Alu::Add, X16, st(offset_of!(DState, delta))));
                        a.e(call_r(X16));
                        a.bind(after);
                    };
                    let callout = |a: &mut Asm, stubs: &mut Vec<(Label, u32)>, callouts: &mut Vec<Callout>, c: Callout| {
                        let n = callouts.len();
                        callouts.push(c);
                        a.regs_to_args(c.arity().min(8));
                        call_out(a, n);
                        a.e(alu_mi(Alu::Cmp, st(offset_of!(DState, trap)), 0));
                        trap(a, stubs, PRIM_FAILED, Cond::Ne);
                    };
                    // A control frame: the link, `second` (the landing, the
                    // return address, or nothing), the marker, REG1 and
                    // REG2, and `last`.
                    let control_frame = |a: &mut Asm, stubs: &mut Vec<(Label, u32)>, second: Option<Reg>, marker: Value, last: Option<usize>| {
                        a.e(sub_imm(SP, CONTROL_FRAME as i32));
                        a.e(store(m(SP, 0), FRAME));
                        match second {
                            Some(r) => a.e(store(m(SP, 8), r)),
                            None => a.e(store_imm(m(SP, 8), 0)),
                        }
                        a.e(mov(FRAME, SP));
                        // A control frame may pass the cache's limit by
                        // half the slack: the next procedure's frame
                        // flushes it with the rest.
                        a.e(lea(X16, m(SP, (STACK_SLACK / 2) as i32)));
                        a.e(alu_rm(Alu::Cmp, X16, st(offset_of!(DState, stack_limit))));
                        trap(a, stubs, STACK_OVERFLOW, Cond::B);
                        a.imm(X16, marker.raw());
                        a.e(store(m(FRAME, 16), X16));
                        a.e(store(m(FRAME, 24), IN_REGS[1]));
                        a.e(store(m(FRAME, 32), IN_REGS[2]));
                        match last {
                            Some(off) => {
                                a.e(load(X16, st(off)));
                                a.e(store(m(FRAME, 40), X16));
                            }
                            None => a.e(store_imm(m(FRAME, 40), 0)),
                        }
                    };
                    let pop_control = |a: &mut Asm| {
                        a.e(load(FRAME, m(SP, 0)));
                        a.e(add_imm(SP, CONTROL_FRAME as i32));
                    };
                    match ROUTINES[k(o(0))].0 {
                        // REG1 the tag, REG2 the handler, REG3 the thunk. An
                        // abort resumes at the landing, the prompt's frame on
                        // top, with the value: the handler called with it.
                        "prompt" => {
                            let (land, after, done, handled) = (a.label(), a.label(), a.label(), a.label());
                            a.lea_l(X9, land);
                            control_frame(&mut a, &mut stubs, Some(X9), PROMPT_MARK, Some(offset_of!(DState, regions)));
                            a.e(mov(CLO, IN_REGS[3]));
                            call_clo(&mut a, &mut foreign, 0, after);
                            pop_control(&mut a);
                            a.jmp(done);
                            a.bind(land);
                            a.e(mov(IN_REGS[1], RESULT));
                            a.e(load(CLO, m(SP, 32)));
                            pop_control(&mut a);
                            call_clo(&mut a, &mut foreign, 1, handled);
                            a.bind(done);
                        }
                        "withmark" => {
                            let after = a.label();
                            control_frame(&mut a, &mut stubs, None, MARK_MARK, None);
                            a.e(mov(CLO, IN_REGS[3]));
                            call_clo(&mut a, &mut foreign, 0, after);
                            pop_control(&mut a);
                        }
                        // In tail position, this frame popped (the return
                        // address on top): the thunk tail-called with the
                        // mark's frame under it, returning through
                        // `mark_ret`; a mark's frame there already, for the
                        // same key, has its value replaced.
                        "withmark-tail" => {
                            let (push_, call, stub, after) = (a.label(), a.label(), a.label(), a.label());
                            a.e(load(X9, st(offset_of!(DState, mark_ret))));
                            a.e(alu_rm(Alu::Cmp, X9, m(SP, 0)));
                            a.jcc(Cond::Ne, push_);
                            a.e(load(X16, m(SP, 8 + 24)));
                            a.e(cmp(X16, IN_REGS[1]));
                            a.jcc(Cond::Ne, push_);
                            a.e(store(m(SP, 8 + 32), IN_REGS[2]));
                            a.jmp(call);
                            a.bind(push_);
                            a.e(pop(X11));
                            control_frame(&mut a, &mut stubs, Some(X11), MARK_MARK, None);
                            a.e(push_m(st(offset_of!(DState, mark_ret))));
                            a.bind(call);
                            a.e(mov(CLO, IN_REGS[3]));
                            a.e(load(X16, fld(CLO, CLOSURE_WORD)));
                            a.e(alu_rm(Alu::Cmp, X16, st(offset_of!(DState, code_lo))));
                            a.jcc(Cond::B, stub);
                            foreign.push((stub, after, 0, true));
                            a.e(alu_rm(Alu::Add, X16, st(offset_of!(DState, delta))));
                            a.e(jmp_r(X16));
                            a.bind(after);
                        }
                        "abort" => {
                            callout(&mut a, &mut stubs, self.callouts, Callout::Abort);
                            uses_resume = true;
                            a.jmp(resume_at);
                        }
                        r @ ("callcc" | "callcomp") => {
                            let after = a.label();
                            a.lea_l(X9, after);
                            a.e(store(st(offset_of!(DState, ret_pc)), X9));
                            let q = self.resume_proc();
                            let f = self.field(p, Field::Code(q));
                            a.field(X9, f);
                            a.e(store(st(offset_of!(DState, aux)), X9));
                            callout(&mut a, &mut stubs, self.callouts, Callout::Capture { whole: r == "callcc", once: false });
                            a.e(mov(IN_REGS[1], RESULT));
                            a.e(load(CLO, st(args)));
                            call_clo(&mut a, &mut foreign, 1, after);
                        }
                        "firstmark" => callout(&mut a, &mut stubs, self.callouts, Callout::FirstMark),
                        "currentmarks" => callout(&mut a, &mut stubs, self.callouts, Callout::CurrentMarks),
                        _ => callout(&mut a, &mut stubs, self.callouts, Callout::MarksOf),
                    }
                }
                // A primitive that never collects, on `RESULT` and `REGk` or
                // a constant: in line, where its fast path can; else a
                // call-out with no collection, the registers kept around it.
                "prim1" | "prim2" | "prim2imm" => {
                    let pn = k(o(0));
                    let pname = fixpt_runtime::PRIMITIVES.get(pn).map_or("?", |d| d.name);
                    if !fixpt_runtime::never_collects(pname) {
                        return decline(format!("`{op}` of `{pname}`, which may collect"));
                    }
                    // Rounding is SSE4.1's, which a few early processors lack.
                    if !sse41() && ["floor", "ceiling", "truncate", "round"].iter().any(|w| pname.ends_with(w)) {
                        return decline(format!("`{pname}` needs SSE4.1, which this processor lacks"));
                    }
                    // An element only `f64` operations use: its bits.
                    if pname == "%fx26-flatarray-ref" && raw_refs[si - 1] {
                        let y = a.get(k(o(1)), X17);
                        let y = if op == "prim2" && y != RESULT {
                            y
                        } else if op == "prim2" {
                            a.e(mov(X17, RESULT));
                            X17
                        } else {
                            a.imm(X17, o(1).raw());
                            X17
                        };
                        let (slow, done) = (a.label(), a.label());
                        flat_element(&mut a, RESULT, y, slow);
                        a.e(load(RESULT, mi(X15, X14, 8, 0)));
                        a.jmp(done);
                        a.bind(slow);
                        pure_call(&mut a, self.callouts, Callout::Pure { p: pn, n: 2 }, &[RESULT, y], RESULT);
                        a.e(alu_mi(Alu::Cmp, st(offset_of!(DState, trap)), 0));
                        trap(&mut a, &mut stubs, PRIM_FAILED, Cond::Ne);
                        unbox_f64(&mut a, RESULT);
                        a.bind(done);
                        continue;
                    }
                    // A blobref's read of a scalar the layout of which is
                    // the constant: in line. An `f64` only `f64`
                    // operations use: its bits.
                    if pname == "%fx26-suffix-ref-get" && op == "prim2imm" && o(1).is_fixnum() {
                        let raw = raw_refs[si - 1];
                        let (slow, done) = (a.label(), a.label());
                        suffix_get(&mut a, o(1).as_fixnum(), raw, slow);
                        a.jmp(done);
                        a.bind(slow);
                        a.imm(X17, o(1).raw());
                        pure_call(&mut a, self.callouts, Callout::Pure { p: pn, n: 2 }, &[RESULT, X17], RESULT);
                        a.e(alu_mi(Alu::Cmp, st(offset_of!(DState, trap)), 0));
                        trap(&mut a, &mut stubs, PRIM_FAILED, Cond::Ne);
                        if raw {
                            unbox_f64(&mut a, RESULT);
                        }
                        a.bind(done);
                        continue;
                    }
                    // A blobref stepped a constant number of bytes along, a
                    // flat sum's numeric tag, or a blobref made: in line.
                    let step = pname == "%suffix-ref+" && o(1).is_fixnum() && (0..1 << 24).contains(&o(1).as_fixnum());
                    let tag = pname == "%fx26-flat-tag" && o(1).is_fixnum();
                    let at = pname == "%suffix-ref" && o(1).is_fixnum() && (0..1 << 26).contains(&o(1).as_fixnum());
                    if op == "prim2imm" && (step || tag || at) {
                        let (slow, done) = (a.label(), a.label());
                        if step {
                            suffix_step(&mut a, o(1).as_fixnum(), slow);
                        } else if tag {
                            flat_tag(&mut a, o(1).as_fixnum(), slow);
                        } else {
                            blobref_at(&mut a, o(1).as_fixnum(), slow);
                        }
                        a.jmp(done);
                        a.bind(slow);
                        a.imm(X17, o(1).raw());
                        pure_call(&mut a, self.callouts, Callout::Pure { p: pn, n: 2 }, &[RESULT, X17], RESULT);
                        a.e(alu_mi(Alu::Cmp, st(offset_of!(DState, trap)), 0));
                        trap(&mut a, &mut stubs, PRIM_FAILED, Cond::Ne);
                        a.bind(done);
                        continue;
                    }
                    // The second operand of a raw operation, in a register
                    // apart from `RESULT`, `RCX` and `RDX`.
                    let second = |a: &mut Asm| match k(o(1)) {
                        0 => {
                            a.e(mov(X17, RESULT));
                            X17
                        }
                        r => a.get(r, X17),
                    };
                    if let Some(super::RawOp::F64 { what }) = reps::raw_op(pname) {
                        match what {
                            "from-int" => f64_of_int(&mut a, self.callouts, pn),
                            "->int" => int_of_f64(&mut a, self.callouts, &mut stubs, pn),
                            _ => {
                                let y = if op == "prim2" { second(&mut a) } else { RESULT };
                                f64_fast(&mut a, what, y);
                            }
                        }
                        continue;
                    }
                    if let Some(super::RawOp::Int { signed, what }) = reps::raw_op(pname) {
                        // A shift's count is an `int`, a bignum maybe: its
                        // low bits, as a fixnum's are, in a copy.
                        let count = matches!(what, "-shl" | "-shr");
                        let count_of = |a: &mut Asm, callouts: &mut Vec<Callout>| {
                            unbox_reg(a, callouts, X17);
                            a.e(shl_imm(X17, 3));
                        };
                        let y = match op {
                            "prim2" if count => {
                                let r = second(&mut a);
                                if r != X17 {
                                    a.e(mov(X17, r));
                                }
                                count_of(&mut a, self.callouts);
                                X17
                            }
                            "prim2" => second(&mut a),
                            "prim2imm" => {
                                let v = o(1);
                                if v.is_fixnum() && !count {
                                    a.imm(X17, v.as_fixnum() as u64);
                                } else if v.is_fixnum() || v.raw() & 7 == 3 {
                                    a.imm(X17, v.raw());
                                } else {
                                    let f = self.field(p, Field::Const(v));
                                    a.field(X17, f);
                                    if count {
                                        count_of(&mut a, self.callouts);
                                    } else {
                                        unbox_reg(&mut a, self.callouts, X17);
                                    }
                                }
                                X17
                            }
                            _ => X17,
                        };
                        if what == "->int" {
                            box_reg(&mut a, self.callouts, RESULT, signed);
                        } else {
                            raw_fast(&mut a, &mut stubs, signed, what, y);
                        }
                        continue;
                    }
                    let y = match op {
                        // Not `RESULT` itself (REG0): the fast paths keep
                        // their operands apart.
                        "prim2" if k(o(1)) == 0 => {
                            a.e(mov(X17, RESULT));
                            X17
                        }
                        "prim2" => a.get(k(o(1)), X17),
                        "prim2imm" => {
                            let v = o(1);
                            if v.is_fixnum() || v.raw() & 7 == 3 {
                                a.imm(X17, v.raw());
                            } else {
                                let f = self.field(p, Field::Const(v));
                                a.field(X17, f);
                            }
                            X17
                        }
                        _ => X17,
                    };
                    let (slow, done) = (a.label(), a.label());
                    let fast_path = pure_fast(&mut a, pname, y, slow);
                    if !fast_path || a.used(slow) {
                        if fast_path {
                            a.jmp(done);
                        }
                        a.bind(slow);
                        let n = if op == "prim1" { 1 } else { 2 };
                        pure_call(&mut a, self.callouts, Callout::Pure { p: pn, n }, &[RESULT, y][..n], RESULT);
                        a.e(alu_mi(Alu::Cmp, st(offset_of!(DState, trap)), 0));
                        trap(&mut a, &mut stubs, PRIM_FAILED, Cond::Ne);
                    }
                    a.bind(done);
                }
                // Of three, `RESULT`, a constant and `REGk`: the primitive.
                "prim3imm" => {
                    let pn = k(o(0));
                    let pname = fixpt_runtime::PRIMITIVES.get(pn).map_or("?", |d| d.name);
                    if !fixpt_runtime::never_collects(pname) {
                        return decline(format!("`{op}` of `{pname}`, which may collect"));
                    }
                    let x = o(1);
                    let z = match k(o(2)) {
                        0 => {
                            a.e(mov(X12, RESULT));
                            X12
                        }
                        r => a.get(r, X12),
                    };
                    let raw = reps::is_f64_set(&o, &prim_name) && reps_in[si - 1][k(o(2))] == Rep::F64;
                    let (slow, done) = (a.label(), a.label());
                    // In line only with `REGk` in a register of its own:
                    // the suffix ref's helpers use `X12` and the rest.
                    let code = x.is_fixnum().then(|| x.as_fixnum()).filter(|_| (1..=3).contains(&k(o(2))));
                    match (pname, code) {
                        ("%fx26-blobref-index", Some(c)) => blobref_index(&mut a, c, z, slow),
                        ("%fx26-suffix-ref-set!", Some(c)) => suffix_store(&mut a, c, z, raw, slow),
                        ("%fx26-flat-variant!", Some(c)) => flat_variant(&mut a, c, z, slow),
                        _ => {}
                    }
                    if a.used(slow) {
                        a.jmp(done);
                    }
                    a.bind(slow);
                    // A raw `f64` boxed for the primitive in a copy: `REGk`
                    // stays raw for what follows.
                    let z = if raw {
                        if z != X12 {
                            a.e(mov(X12, z));
                        }
                        box_f64(&mut a, self.callouts, X12);
                        X12
                    } else {
                        z
                    };
                    if x.is_fixnum() || x.raw() & 7 == 3 {
                        a.imm(X17, x.raw());
                    } else {
                        let f = self.field(p, Field::Const(x));
                        a.field(X17, f);
                    }
                    pure_call(&mut a, self.callouts, Callout::Pure { p: pn, n: 3 }, &[RESULT, X17, z], RESULT);
                    a.e(alu_mi(Alu::Cmp, st(offset_of!(DState, trap)), 0));
                    trap(&mut a, &mut stubs, PRIM_FAILED, Cond::Ne);
                    a.bind(done);
                }
                // A call-out: to Rust, on Rust's stack, which may collect;
                // everything live is in the frame by then, and the
                // arguments go through the state.
                "prim" | "cellular" | "lambda" => {
                    let mut code_field = None;
                    let routine = if op == "lambda" { None } else { ROUTINES.get(k(o(0))).map(|r| r.0) };
                    let c = match (op, routine) {
                        ("lambda", _) => {
                            let q = self.proc_of(o(0)).map_err(|e| format!("`{name}` makes a closure of {e}"))?;
                            code_field = Some(self.field(p, Field::Code(q)));
                            Callout::Closure { n: k(o(1)) }
                        }
                        ("cellular", Some("cons")) if k(o(1)) == 2 => Callout::Cons,
                        ("cellular", Some("rest")) if k(o(1)) == 0 => Callout::Rest,
                        ("cellular", Some("field@")) if k(o(1)) == 2 => Callout::FieldRef,
                        ("prim", _) => match fixpt_runtime::PRIMITIVES.get(k(o(0))) {
                            Some(d) if d.name == "%region-closure" => Callout::RegionClosure { n: k(o(1)) },
                            Some(d) if d.name == "%stay-cellular" => return decline("it calls `stay-cellular`".into()),
                            Some(d) if matches!(d.kind, fixpt_runtime::PrimKind::Simple(_)) && d.accepts(k(o(1))) => {
                                Callout::Prim { p: k(o(0)), n: k(o(1)) }
                            }
                            Some(d) => return decline(format!("the primitive `{}`", d.name)),
                            None => return decline(format!("primitive {}", k(o(0)))),
                        },
                        (_, r) => return decline(format!("the routine `{}`", r.unwrap_or("?"))),
                    };
                    let leaf_closure = frame.is_none() && matches!(c, Callout::Closure { .. });
                    if frame.is_none() && !leaf_closure {
                        return decline("a call-out outside a frame".into());
                    }
                    let (r1, r2, r3) = (IN_REGS[1], IN_REGS[2], IN_REGS[3]);
                    let prim_is = |want: &str, n: usize| matches!(c, Callout::Prim { p, n: m } if m == n && fixpt_runtime::PRIMITIVES[p].name == want);
                    let done = a.label();
                    let slow = a.label();
                    // Room for `n` words from the heap's free space, short
                    // of the collection's threshold: at X11, the free space
                    // bumped; else `slow`. Uses X9, X13, X14, X16.
                    let bump = |a: &mut Asm, n: i32| {
                        a.e(load(X13, st(offset_of!(DState, top))));
                        a.e(load(X14, m(X13, 0)));
                        a.e(lea(X16, m(X14, n)));
                        a.e(alu_rm(Alu::Cmp, X16, st(offset_of!(DState, alloc_limit))));
                        a.jcc(Cond::A, slow);
                        a.e(load(X9, st(offset_of!(DState, words))));
                        a.e(lea(X11, mi(X9, X14, 8, 0)));
                        a.e(store(m(X13, 0), X16));
                    };
                    // `rcons`: in the region's current chunk, as `procedure`'s.
                    if prim_is("%region-cons", 3) {
                        a.e(test_imm(r1, 7));
                        a.jcc(Cond::Ne, slow);
                        a.e(cmp_imm(r1, 8 * fixpt_heap::heap::REGION_SLOTS as i32));
                        a.jcc(Cond::Ae, slow);
                        a.e(load(X13, st(offset_of!(DState, region_table))));
                        a.e(lea(X13, mi(X13, r1, 2, 0)));
                        a.e(load(X14, m(X13, 0)));
                        a.e(lea(X16, m(X14, 2)));
                        a.e(alu_rm(Alu::Cmp, X16, m(X13, 8)));
                        a.jcc(Cond::A, slow);
                        a.e(load(X9, st(offset_of!(DState, words))));
                        a.e(lea(X11, mi(X9, X14, 8, 0)));
                        a.e(store(m(X11, 0), r2));
                        a.e(store(m(X11, 8), r3));
                        a.e(store(m(X13, 0), X16));
                        a.e(lea(RESULT, m(X11, fixpt_heap::value::TAG_PAIR as i32)));
                        a.jmp(done);
                    }
                    // A raw `f64` to store is boxed only if the call-out
                    // must do it.
                    let raw_store = reps_in[si - 1][3] == Rep::F64;
                    if prim_is("%fx26-flatarray-set!", 3) {
                        flat_set(&mut a, slow, done, raw_store);
                    }
                    if prim_is("%fx26-suffix-ref-set!", 3) {
                        suffix_set(&mut a, slow, done);
                    }
                    if prim_is("%fx26-suffix-ref-index", 3) {
                        suffix_index(&mut a, slow);
                        a.jmp(done);
                    }
                    // `int`'s bit operations of fixnums.
                    if let Callout::Prim { p, n } = c
                        && let bop @ ("%fx26-bitwise-and" | "%fx26-bitwise-ior" | "%fx26-bitwise-xor" | "%fx26-bitwise-not") = fixpt_runtime::PRIMITIVES[p].name
                    {
                        if n == 2 {
                            a.e(mov(X13, r1));
                            a.e(or(X13, r2));
                            a.e(test_imm(X13, 7));
                        } else {
                            a.e(test_imm(r1, 7));
                        }
                        a.jcc(Cond::Ne, slow);
                        a.e(mov(RESULT, r1));
                        match bop {
                            "%fx26-bitwise-and" => a.e(and(RESULT, r2)),
                            "%fx26-bitwise-ior" => a.e(or(RESULT, r2)),
                            "%fx26-bitwise-xor" => a.e(xor(RESULT, r2)),
                            _ => {
                                a.e(neg(RESULT));
                                a.e(sub_imm(RESULT, 8));
                            }
                        }
                        a.jmp(done);
                    }
                    // A mutable bloblet of no suffix (`%make-bloblet`).
                    if let Callout::Prim { p, n } = c
                        && fixpt_runtime::PRIMITIVES[p].name == "%make-bloblet"
                        && (1..=fixpt_heap::layout::regcode::REGS).contains(&n)
                    {
                        let total = n;
                        a.e(test(r1, r1));
                        a.jcc(Cond::Ne, slow);
                        bump(&mut a, 1 + total as i32);
                        let hd = fixpt_heap::value::make_header(const { fixpt_heap::layout::kind("bloblet") }, total, 0);
                        a.imm(X15, hd);
                        a.e(store(m(X11, 0), X15));
                        for j in 2..=n {
                            a.store_reg(m(X11, 8 * (1 + total - j) as i32), j, X17);
                        }
                        let t = fixpt_heap::layout::T_DISTANCE.put(fixpt_heap::value::TAG_TRAILER, total as u64);
                        a.imm(X15, t);
                        a.e(store(m(X11, 8 * total as i32), X15));
                        a.e(lea(RESULT, m(X11, (8 * (1 + total) + fixpt_heap::value::TAG_BLOBLET as usize) as i32)));
                        a.jmp(done);
                    }
                    // A sum or product (`%make-frozen`).
                    if let Callout::Prim { p, n } = c
                        && fixpt_runtime::PRIMITIVES[p].name == "%make-frozen"
                        && (2..=fixpt_heap::layout::regcode::REGS).contains(&n)
                    {
                        use fixpt_heap::layout::{H_FIELDS_FROZEN, H_SUFFIX_FROZEN, kind};
                        let total = n;
                        let (sum_k, product_k) = (const { kind("sum") }, const { kind("product") });
                        let header = |kd: u8| H_SUFFIX_FROZEN.put(H_FIELDS_FROZEN.put(fixpt_heap::value::make_header(kd, total, 0), 1), 1);
                        let (sum, kinded) = (a.label(), a.label());
                        a.cmp_k(r1, Value::fixnum(sum_k as i64).raw());
                        a.jcc(Cond::E, sum);
                        a.cmp_k(r1, Value::fixnum(product_k as i64).raw());
                        a.jcc(Cond::Ne, slow);
                        a.imm(X17, header(product_k));
                        a.jmp(kinded);
                        a.bind(sum);
                        a.imm(X17, header(sum_k));
                        a.bind(kinded);
                        bump(&mut a, 1 + total as i32);
                        a.e(store(m(X11, 0), X17));
                        for j in 2..=n {
                            a.store_reg(m(X11, 8 * (1 + total - j) as i32), j, X17);
                        }
                        let t = fixpt_heap::layout::T_DISTANCE.put(fixpt_heap::value::TAG_TRAILER, total as u64);
                        a.imm(X15, t);
                        a.e(store(m(X11, 8 * total as i32), X15));
                        a.e(lea(RESULT, m(X11, (8 * (1 + total) + fixpt_heap::value::TAG_BLOBLET as usize) as i32)));
                        a.jmp(done);
                    }
                    if let Callout::Cons = c {
                        bump(&mut a, 2);
                        a.e(store(m(X11, 0), r1));
                        a.e(store(m(X11, 8), r2));
                        a.e(lea(RESULT, m(X11, fixpt_heap::value::TAG_PAIR as i32)));
                        a.jmp(done);
                    }
                    // Field REG2 (8k) of the bloblet in REG1, 2 ≤ k ≤ F.
                    if let Callout::FieldRef = c {
                        let tag = fixpt_heap::value::TAG_TRAILER as i32;
                        a.e(load(X16, fld(r1, 1)));
                        a.e(mov(X13, X16));
                        a.e(and_imm(X13, 7));
                        a.e(cmp_imm(X13, tag));
                        a.jcc(Cond::Ne, slow);
                        a.e(cmp_imm(r2, 16));
                        a.jcc(Cond::L, slow);
                        a.e(sub_imm(X16, tag));
                        a.e(cmp(r2, X16));
                        a.jcc(Cond::G, slow);
                        a.e(mov(X11, r1));
                        a.e(sub(X11, r2));
                        a.e(load(RESULT, m(X11, -4)));
                        a.jmp(done);
                    }
                    // `%bloblet-set!`: REG3 into field REG2 (8k) of the
                    // bloblet in REG1, its fields not frozen.
                    if prim_is("%bloblet-set!", 3) {
                        let tag = fixpt_heap::value::TAG_TRAILER as i32;
                        a.e(load(X16, fld(r1, 1)));
                        a.e(mov(X13, X16));
                        a.e(and_imm(X13, 7));
                        a.e(cmp_imm(X13, tag));
                        a.jcc(Cond::Ne, slow);
                        a.e(cmp_imm(r2, 16));
                        a.jcc(Cond::L, slow);
                        a.e(sub_imm(X16, tag));
                        a.e(cmp(r2, X16));
                        a.jcc(Cond::G, slow);
                        a.e(mov(X11, r1));
                        a.e(sub(X11, X16));
                        a.e(load(X13, m(X11, -12)));
                        a.e(shr_imm(X13, fixpt_heap::layout::H_FIELDS_FROZEN.lo as u8));
                        a.e(test_imm(X13, 1));
                        a.jcc(Cond::Ne, slow);
                        a.e(mov(X11, r1));
                        a.e(sub(X11, r2));
                        a.e(store(m(X11, -4), r3));
                        a.es(&card_mark(X11, -4, ST, offset_of!(DState, cards) as i32, X13, X16));
                        a.imm(RESULT, Value::UNSPECIFIED.raw());
                        a.jmp(done);
                    }
                    // A native closure over REG1…REGn from the free space.
                    if let (Callout::Closure { n }, Some(f)) = (c, code_field)
                        && n <= 8
                    {
                        let total = n + 2;
                        bump(&mut a, (total + 1) as i32);
                        let header = fixpt_heap::value::make_header(const { fixpt_heap::layout::kind("native-closure") }, total, 0);
                        a.imm(X17, header);
                        a.e(store(m(X11, 0), X17));
                        for i in 0..n {
                            a.store_reg(m(X11, 8 * (n - i) as i32), 1 + i, X17);
                        }
                        a.field(X17, f);
                        a.e(store(m(X11, 8 * (n + 1) as i32), X17));
                        let trailer = fixpt_heap::layout::T_DISTANCE.put(fixpt_heap::value::TAG_TRAILER, total as u64);
                        a.imm(X17, trailer);
                        a.e(store(m(X11, 8 * total as i32), X17));
                        a.e(lea(RESULT, m(X11, (8 * (total + 1)) as i32 + fixpt_heap::value::TAG_BLOBLET as i32)));
                        a.jmp(done);
                    }
                    a.bind(slow);
                    if raw_store && prim_is("%fx26-flatarray-set!", 3) {
                        box_f64(&mut a, self.callouts, IN_REGS[3]);
                    }
                    if let (Callout::Closure { n }, Some(f)) = (c, code_field) {
                        if leaf_closure {
                            // A frame for the collector to walk, with
                            // nothing in it, under the return address.
                            small_frame(&mut a);
                        }
                        a.field(X17, f);
                        a.imm(X9, n as u64);
                        a.e(call_m(st(offset_of!(DState, closure))));
                        if leaf_closure {
                            a.e(load(FRAME, m(SP, 0)));
                            a.e(add_imm(SP, 8));
                        }
                    } else {
                        let n = self.callouts.len();
                        self.callouts.push(c);
                        a.regs_to_args(c.arity().min(8));
                        call_out(&mut a, n);
                        a.e(alu_mi(Alu::Cmp, st(offset_of!(DState, trap)), 0));
                        trap(&mut a, &mut stubs, PRIM_FAILED, Cond::Ne);
                    }
                    a.bind(done);
                }
                // A call, as `procedure` makes it: `call` in place of `blr`,
                // `jmp` of `br`, the return address already on top for a
                // tail call (the frame popped pushed it back).
                "invoke" | "tailinvoke" => {
                    let tail = op == "tailinvoke";
                    let (stub, after) = (a.label(), a.label());
                    let not_native = |a: &mut Asm| {
                        a.e(load(X16, fld(CLO, CLOSURE_WORD)));
                        a.e(alu_rm(Alu::Cmp, X16, st(offset_of!(DState, code_lo))));
                        a.jcc(Cond::B, stub);
                    };
                    if let Some((cell, writes)) = bound.take() {
                        let (slow, join) = (a.label(), a.label());
                        let fc = self.field(p, Field::Cell(cell));
                        a.field(X9, fc);
                        a.e(load(CLO, fld(X9, 2)));
                        a.e(load(X11, fld(X9, GLOBAL_WRITES)));
                        a.imm(X16, writes.raw());
                        a.e(cmp(X11, X16));
                        a.jcc(Cond::Ne, slow);
                        match pending.take() {
                            Some(Field::Code(q)) => {
                                let f = self.field(p, Field::Code(q));
                                a.field(X16, f);
                            }
                            Some(g) => {
                                let f = self.field(p, g);
                                a.field(CLO, f);
                                a.e(load(X16, fld(CLO, CLOSURE_WORD)));
                            }
                            None => unreachable!("a global bound is called"),
                        }
                        a.bind(join);
                        cell_slows.push((slow, join, stub));
                        foreign.push((stub, after, k(o(0)), tail));
                    } else {
                        match pending.take() {
                            Some(Field::Code(q)) => {
                                let f = self.field(p, Field::Code(q));
                                a.field(X16, f);
                            }
                            Some(Field::Cell(c)) => {
                                let f = self.field(p, Field::Cell(c));
                                a.field(X9, f);
                                a.e(load(CLO, fld(X9, 2)));
                                not_native(&mut a);
                                foreign.push((stub, after, k(o(0)), tail));
                            }
                            Some(g) => {
                                let f = self.field(p, g);
                                a.field(CLO, f);
                                a.e(load(X16, fld(CLO, CLOSURE_WORD)));
                            }
                            None => {
                                a.e(mov(CLO, RESULT));
                                not_native(&mut a);
                                foreign.push((stub, after, k(o(0)), tail));
                            }
                        }
                    }
                    // The count, for a variadic callee (`vargs`).
                    a.imm(X9, k(o(0)) as u64);
                    a.e(alu_rm(Alu::Add, X16, st(offset_of!(DState, delta))));
                    a.e(if tail { jmp_r(X16) } else { call_r(X16) });
                    a.bind(after);
                }
                "invokeself" => {
                    if let Some(s) = clo_slot.filter(|_| captures) {
                        a.e(load(CLO, m(FRAME, s)));
                    }
                    a.call_l(entry);
                }
                "return" => a.e(ret()),
                "branch" | "branchf" | "brancht" => {
                    let to = (i as i64 + 2 + o(0).as_fixnum()) as usize;
                    let l = edge(&mut a, si - 1, to);
                    if op != "branch" {
                        a.cmp_k(RESULT, Value::FALSE.raw());
                        a.jcc(if op == "branchf" { Cond::E } else { Cond::Ne }, l);
                    } else {
                        if back_to[to] {
                            fuel(&mut a, &mut stubs);
                        }
                        a.jmp(l);
                    }
                }
                other => return decline(format!("`{other}`")),
            }
        }
        a.bind(labels[cells.len()]);
        }
        // The ints' slow paths.
        for slow in int_slows {
            slow.emit(&mut a, self.callouts, &mut stubs);
        }
        // The ways in that test for fixnums, going over to the general
        // version where one is not.
        for (l, unbox, check, to, general) in edge_stubs {
            a.bind(l);
            for (r, rep) in unbox {
                unbox_to(&mut a, self.callouts, r, rep);
            }
            for r in check {
                check_fixnum(&mut a, r, general);
            }
            a.jmp(to);
        }
        let own = a.here();
        for (slow, join, stub) in &cell_slows {
            a.bind(*slow);
            a.e(load(X16, fld(CLO, CLOSURE_WORD)));
            a.e(alu_rm(Alu::Cmp, X16, st(offset_of!(DState, code_lo))));
            a.jcc(Cond::B, *stub);
            a.jmp(*join);
        }
        for (stub, after, n, tail) in &foreign {
            a.bind(*stub);
            a.imm(X9, *n as u64);
            if *tail {
                a.e(jmp_m(st(offset_of!(DState, foreign))));
            } else {
                a.e(call_m(st(offset_of!(DState, foreign))));
                a.jmp(*after);
            }
        }
        if uses_resume {
            a.bind(resume_at);
            resume(&mut a);
        }
        let info = overflow_info(self.procs[p].arity, captures);
        for (over, back) in &overflows {
            a.bind(*over);
            a.field(X16, 1);
            a.imm(X17, info);
            a.e(call_m(st(offset_of!(DState, overflow))));
            a.jmp(*back);
        }
        // The traps, out of the way: a stub per site, calling its kind's
        // stub, which goes to the machine's common trap.
        let kinds: Vec<Label> = (0..TRAPS.len()).map(|_| a.label()).collect();
        for (l, code) in &stubs {
            a.bind(*l);
            a.call_l(kinds[*code as usize]);
        }
        for (code, l) in kinds.iter().enumerate().skip(1) {
            if !stubs.iter().any(|(_, c)| *c as usize == code) {
                continue;
            }
            a.bind(*l);
            a.imm(X9, code as u64);
            a.e(jmp_m(st(offset_of!(DState, trap_stub))));
        }
        self.procs[p].code = a.finish()?;
        self.procs[p].len = own;
        Ok(())
    }
}

/// The slow path of an `int` operation, as `super::IntSlow`.
struct IntSlow {
    entry: Label,
    overflow: Option<Label>,
    back: Label,
    x: Reg,
    y: Reg,
    imm: Option<i32>,
    into: Reg,
    prim: usize,
    sub: bool,
    branch: Option<(Label, bool)>,
}

impl IntSlow {
    fn emit(&self, a: &mut Asm, callouts: &mut Vec<Callout>, stubs: &mut Vec<(Label, u32)>) {
        // A sum written over its operand: the operand again, the wrapped
        // sum undone.
        if let Some(ov) = self.overflow {
            a.bind(ov);
            if self.into == self.x {
                let undo = if self.sub { Alu::Add } else { Alu::Sub };
                match self.imm {
                    Some(n) => a.e(alu_imm(undo, self.x, n)),
                    None => a.e(alu(undo, self.x, self.y)),
                }
            }
        }
        a.bind(self.entry);
        let y = match self.imm {
            Some(n) => {
                a.imm(X16, n as i64 as u64);
                X16
            }
            None => self.y,
        };
        pure_call(a, callouts, Callout::Pure { p: self.prim, n: 2 }, &[self.x, y], self.into);
        a.e(alu_mi(Alu::Cmp, st(offset_of!(DState, trap)), 0));
        let l = a.label();
        stubs.push((l, PRIM_FAILED));
        a.jcc(Cond::Ne, l);
        if let Some((l, when_true)) = self.branch {
            a.cmp_k(RESULT, Value::TRUE.raw());
            a.jcc(if when_true { Cond::E } else { Cond::Ne }, l);
        }
        a.jmp(self.back);
    }
}

/// `REGr` (r ≥ 1) tested for a fixnum, to `general` if it is not one.
fn check_fixnum(a: &mut Asm, r: usize, general: Label) {
    let r = a.get(r, X16);
    check_reg(a, r, general);
}

fn check_reg(a: &mut Asm, r: Reg, general: Label) {
    a.e(test_imm(r, 7));
    a.jcc(Cond::Ne, general);
}

/// Call-out `c`, which never collects, on `args` (registers, put in the
/// state), its value into `into`: `RESULT` and REG1…REG3, which Rust may
/// change, kept in the state around it (REG4…REG8 are there already, and
/// the closure is in a register Rust keeps).
fn pure_call(a: &mut Asm, callouts: &mut Vec<Callout>, c: Callout, args: &[Reg], into: Reg) {
    let n = callouts.len();
    callouts.push(c);
    let base = offset_of!(DState, args);
    for (j, &r) in args.iter().enumerate() {
        a.e(store(st(base + 8 * j), r));
    }
    keep(a, 4, false);
    call_out(a, n);
    a.e(mov(X17, RESULT));
    keep(a, 4, true);
    if into != X17 {
        a.e(mov(into, X17));
    }
}

/// `procedure`'s `shape_fast`: a shape predicate of `RESULT`, in line.
fn shape_fast(a: &mut Asm, name: &str, slow: Label) -> bool {
    use fixpt_heap::layout::kind;
    use fixpt_heap::value::{TAG_BLOBLET, TAG_HEADER, TAG_PAIR, TAG_TRAILER};
    let x = RESULT;
    let kinds: &[u8] = match name {
        "null?" => {
            a.cmp_k(x, Value::NULL.raw());
            a.flag(Cond::E, X15);
            return true;
        }
        "pair?" => {
            a.e(mov(X13, x));
            a.e(and_imm(X13, 7));
            a.e(cmp_imm(X13, TAG_PAIR as i32));
            a.flag(Cond::E, X15);
            return true;
        }
        "char?" | "%fx26-f32?" => {
            a.e(movzx8(X13, x));
            let tag = if name == "char?" { Value::char('\0') } else { Value::f32(0.0) };
            a.e(cmp_imm(X13, (tag.raw() & 0xFF) as i32));
            a.flag(Cond::E, X15);
            return true;
        }
        "boolean?" => {
            a.imm(X15, Value::FALSE.raw());
            a.imm(X16, Value::TRUE.raw());
            a.e(mov(X13, X15));
            a.e(cmp(x, X15));
            a.e(cmov(Cond::E, X13, X16));
            a.e(cmp(x, X16));
            a.e(cmov(Cond::E, X13, X16));
            a.e(mov(RESULT, X13));
            return true;
        }
        "exact-integer?" => &[const { kind("bignum") }],
        "symbol?" => &[const { kind("symbol") }],
        "string?" => &[const { kind("string") }],
        "%fx26-array?" => &[const { kind("bloblet") }],
        "%fx26-box?" => &[const { kind("box") }],
        "%fx26-sum?" => &[const { kind("sum") }],
        "%fx26-product?" => &[const { kind("product") }],
        "%fx26-procedure?" => &[
            const { kind("closure") },
            const { kind("primitive") },
            const { kind("continuation") },
            const { kind("cellular-closure") },
            const { kind("native-closure") },
            const { kind("cellular-continuation") },
        ],
        _ => return false,
    };
    let (yes, no, have, end) = (a.label(), a.label(), a.label(), a.label());
    if name == "exact-integer?" {
        a.e(test_imm(x, 7));
        a.jcc(Cond::E, yes);
    }
    a.e(mov(X13, x));
    a.e(and_imm(X13, 7));
    a.e(cmp_imm(X13, TAG_BLOBLET as i32));
    a.jcc(Cond::Ne, no);
    a.e(load(X16, fld(x, 1)));
    a.e(mov(X13, X16));
    a.e(and_imm(X13, 7));
    a.e(cmp_imm(X13, TAG_HEADER as i32));
    a.jcc(Cond::E, have);
    a.e(cmp_imm(X13, TAG_TRAILER as i32));
    a.jcc(Cond::Ne, slow);
    a.e(sub_imm(X16, TAG_TRAILER as i32));
    a.e(mov(X14, x));
    a.e(sub(X14, X16));
    a.e(load(X16, fld(X14, 1)));
    a.bind(have);
    let kf = fixpt_heap::layout::H_KIND;
    a.e(mov(X13, X16));
    a.e(shr_imm(X13, kf.lo as u8));
    a.e(and_imm(X13, ((1u64 << kf.width) - 1) as i32));
    a.e(cmp_imm(X13, fixpt_heap::layout::KIND_EXTENSION as i32));
    a.jcc(Cond::E, slow);
    for &c in kinds {
        a.e(cmp_imm(X13, c as i32));
        a.jcc(Cond::E, yes);
    }
    a.bind(no);
    a.imm(RESULT, Value::FALSE.raw());
    a.jmp(end);
    a.bind(yes);
    a.imm(RESULT, Value::TRUE.raw());
    a.bind(end);
    true
}

/// `procedure`'s `pure_fast`, of what x86_64 has so far: the shape
/// predicates, and fixnums' `*`, `quotient`, `modulo`, `arithmetic-shift`
/// and a bloblet's count of fields. `RESULT` and `y` (neither `RCX` nor
/// `RDX`, and `y` not `RESULT`) as they were on the way to `slow`.
fn pure_fast(a: &mut Asm, name: &str, y: Reg, slow: Label) -> bool {
    let x = RESULT;
    if shape_fast(a, name, slow) {
        return true;
    }
    let fixnums = |a: &mut Asm| {
        a.e(mov(X13, x));
        a.e(or(X13, y));
        a.e(test_imm(X13, 7));
        a.jcc(Cond::Ne, slow);
    };
    match name {
        // A product in 61 bits: the 64-bit one did not overflow.
        "%fx26-mul" => {
            fixnums(a);
            a.e(mov(X14, y));
            a.e(sar_imm(X14, 3));
            a.e(mov(X13, x));
            a.e(imul(X13, X14));
            a.jcc(Cond::O, slow);
            a.e(mov(RESULT, X13));
        }
        // The raw values' quotient is the quotient's value, their
        // remainder the remainder's raw value. `idiv` takes `RESULT`, kept
        // in `X16` for the slow path.
        "%fx26-quotient" | "modulo" => {
            fixnums(a);
            a.e(test(y, y));
            a.jcc(Cond::E, slow);
            a.e(mov(X16, x));
            a.e(cqo());
            a.e(idiv(y));
            if name == "%fx26-quotient" {
                let (ok, restore) = (a.label(), a.label());
                a.e(mov(X13, RAX));
                a.e(shl_imm(X13, 3));
                a.e(sar_imm(X13, 3));
                a.e(cmp(X13, RAX));
                a.jcc(Cond::Ne, restore);
                a.e(shl_imm(RAX, 3));
                a.jmp(ok);
                a.bind(restore);
                a.e(mov(RESULT, X16));
                a.jmp(slow);
                a.bind(ok);
            } else {
                let signed = a.label();
                a.e(test(RDX, RDX));
                a.jcc(Cond::E, signed);
                a.e(mov(X13, RDX));
                a.e(xor(X13, y));
                a.jcc(Cond::Ns, signed);
                a.e(add(RDX, y));
                a.bind(signed);
                a.e(mov(RESULT, RDX));
            }
        }
        // Left while the result stays a fixnum; right (floor) by fewer
        // than 63.
        "%fx26-arithmetic-shift" => {
            fixnums(a);
            let (right, done) = (a.label(), a.label());
            a.e(mov(RCX, y));
            a.e(sar_imm(RCX, 3));
            a.e(test(RCX, RCX));
            a.jcc(Cond::L, right);
            a.e(cmp_imm(RCX, 61));
            a.jcc(Cond::Ge, slow);
            a.e(mov(X14, x));
            a.e(shift_cl(Shift::Shl, X14));
            a.e(mov(X16, X14));
            a.e(shift_cl(Shift::Sar, X16));
            a.e(cmp(X16, x));
            a.jcc(Cond::Ne, slow);
            a.e(mov(RESULT, X14));
            a.jmp(done);
            a.bind(right);
            a.e(neg(RCX));
            a.e(cmp_imm(RCX, 63));
            a.jcc(Cond::Ae, slow);
            a.e(mov(X14, x));
            a.e(shift_cl(Shift::Sar, X14));
            a.e(sar_imm(X14, 3));
            a.e(shl_imm(X14, 3));
            a.e(mov(RESULT, X14));
            a.bind(done);
        }
        "%fx26-flatarray-length" => {
            flat_count(a, x, X13);
            a.e(shl_imm(X13, 3));
            a.e(mov(RESULT, X13));
        }
        "%fx26-flatarray-ref" => flat_ref(a, y, slow),
        // A suffix ref's offset, and its owner, a bloblet.
        "%suffix-ref-offset" | "%suffix-ref-owner" => {
            a.e(mov(X16, x));
            a.e(and_imm(X16, 7));
            a.e(cmp_imm(X16, fixpt_heap::value::TAG_SUFFIX_REF as i32));
            a.jcc(Cond::Ne, slow);
            if name == "%suffix-ref-offset" {
                a.e(mov(X13, x));
                a.e(shr_imm(X13, fixpt_heap::value::SUFFIX_OFFSET_SHIFT as u8));
                a.e(shl_imm(X13, 3));
                a.e(mov(RESULT, X13));
            } else {
                ubfx(a, X14, x, 3, fixpt_heap::value::SUFFIX_OWNER_BITS);
                a.e(load(X9, st(offset_of!(DState, words))));
                a.e(lea(RESULT, mi(X9, X14, 8, fixpt_heap::value::TAG_BLOBLET as i32)));
            }
        }
        // `y` bytes along: still in the owner's suffix, the offset rebuilt.
        "%suffix-ref+" => {
            a.e(test_imm(y, 7));
            a.jcc(Cond::Ne, slow);
            suffix_owner(a, x, slow);
            a.e(mov(X9, y));
            a.e(sar_imm(X9, 3));
            a.e(add(X9, X15));
            a.e(cmp(X9, X13));
            a.jcc(Cond::Ae, slow);
            ubfx(a, X14, x, 0, fixpt_heap::value::SUFFIX_OFFSET_SHIFT);
            a.e(shl_imm(X9, fixpt_heap::value::SUFFIX_OFFSET_SHIFT as u8));
            a.e(mov(RESULT, X14));
            a.e(or(RESULT, X9));
        }
        // A bloblet's count of fields: its trailer's distance.
        "%bloblet-fields" => {
            a.e(mov(X13, x));
            a.e(and_imm(X13, 7));
            a.e(cmp_imm(X13, fixpt_heap::value::TAG_BLOBLET as i32));
            a.jcc(Cond::Ne, slow);
            a.e(load(X16, fld(x, 1)));
            a.e(mov(X13, X16));
            a.e(and_imm(X13, 7));
            a.e(cmp_imm(X13, fixpt_heap::value::TAG_TRAILER as i32));
            a.jcc(Cond::Ne, slow);
            let t = fixpt_heap::layout::T_DISTANCE;
            a.e(shr_imm(X16, t.lo as u8));
            a.e(mov(X13, X16));
            a.e(shl_imm(X13, 32));
            a.e(shr_imm(X13, 29));
            a.e(mov(RESULT, X13));
        }
        _ => return narrow_fast(a, name, y, slow),
    }
    true
}

// ------------------------------------------------------ raw values (`reps`)

/// `f` on `REGr` in a register: its own, or `X12`, loaded first and stored
/// back after (`X12` is kept by Rust, so a call-out in `f` keeps it).
fn in_place(a: &mut Asm, r: usize, f: impl FnOnce(&mut Asm, Reg)) {
    match loc(r) {
        Loc::R(x) => f(a, x),
        Loc::M(mem) => {
            a.e(load(X12, mem));
            f(a, X12);
            a.e(store(mem, X12));
        }
    }
}

/// `d` := bits `lo` to `lo + width − 1` of `s`, as arm64's `ubfx`.
fn ubfx(a: &mut Asm, d: Reg, s: Reg, lo: u32, width: u32) {
    if d != s {
        a.e(mov(d, s));
    }
    if lo + width < 64 {
        a.e(shl_imm(d, (64 - lo - width) as u8));
        a.e(shr_imm(d, (64 - width) as u8));
    } else if lo > 0 {
        a.e(shr_imm(d, lo as u8));
    }
}

/// Register `r`'s raw `i64` (signed) or `u64` boxed, in place: a fixnum
/// where it fits, else a bignum, made by a call-out.
fn box_reg(a: &mut Asm, callouts: &mut Vec<Callout>, r: Reg, signed: bool) {
    let (slow, done) = (a.label(), a.label());
    if signed {
        a.e(mov(X16, r));
        a.e(shl_imm(X16, 3));
        a.e(mov(X13, X16));
        a.e(sar_imm(X13, 3));
        a.e(cmp(X13, r));
        a.jcc(Cond::Ne, slow);
        a.e(mov(r, X16));
    } else {
        a.e(mov(X13, r));
        a.e(shr_imm(X13, 60));
        a.jcc(Cond::Ne, slow);
        a.e(shl_imm(r, 3));
    }
    a.jmp(done);
    a.bind(slow);
    pure_call(a, callouts, Callout::Box { signed }, &[r], r);
    a.bind(done);
}

/// Register `r`'s exact integer unboxed, in place: its low 64 bits, a
/// fixnum's by a shift, a bignum's by a call-out.
fn unbox_reg(a: &mut Asm, callouts: &mut Vec<Callout>, r: Reg) {
    let (slow, done) = (a.label(), a.label());
    a.e(test_imm(r, 7));
    a.jcc(Cond::Ne, slow);
    a.e(sar_imm(r, 3));
    a.jmp(done);
    a.bind(slow);
    pure_call(a, callouts, Callout::Unbox, &[r], r);
    a.bind(done);
}

/// Register `r`'s flonum unboxed, in place: its double's bits; anything
/// but a bloblet gives 0, and is not read.
fn unbox_f64(a: &mut Asm, r: Reg) {
    let (other, done) = (a.label(), a.label());
    a.e(mov(X16, r));
    a.e(and_imm(X16, 7));
    a.e(cmp_imm(X16, fixpt_heap::value::TAG_BLOBLET as i32));
    a.jcc(Cond::Ne, other);
    a.e(load(r, m(r, -4)));
    a.jmp(done);
    a.bind(other);
    a.imm(r, 0);
    a.bind(done);
}

/// Register `r`'s raw `f64` boxed, in place: a flonum from the free space
/// when there is room, else by a call-out that does not collect. Uses X11
/// and X13 to X17.
fn box_f64(a: &mut Asm, callouts: &mut Vec<Callout>, r: Reg) {
    let (slow, done) = (a.label(), a.label());
    a.e(load(X13, st(offset_of!(DState, top))));
    a.e(load(X14, m(X13, 0)));
    a.e(lea(X16, m(X14, 2)));
    a.e(alu_rm(Alu::Cmp, X16, st(offset_of!(DState, alloc_limit))));
    a.jcc(Cond::A, slow);
    a.e(load(X17, st(offset_of!(DState, words))));
    a.e(lea(X11, mi(X17, X14, 8, 0)));
    a.imm(X17, fixpt_heap::value::make_header(fixpt_heap::ObjType::Flonum as u8, 0, 8));
    a.e(store(m(X11, 0), X17));
    a.e(store(m(X11, 8), r));
    a.e(store(m(X13, 0), X16));
    a.e(lea(r, m(X11, 8 + fixpt_heap::value::TAG_BLOBLET as i32)));
    a.jmp(done);
    a.bind(slow);
    pure_call(a, callouts, Callout::BoxF64, &[r], r);
    a.bind(done);
}

/// An `f64` boxed from the free space into `RESULT`, its bits in X9; to
/// `slow` when there is no room. Uses X11 and X13 to X17.
fn box_bits(a: &mut Asm, slow: Label) {
    a.e(load(X13, st(offset_of!(DState, top))));
    a.e(load(X14, m(X13, 0)));
    a.e(lea(X16, m(X14, 2)));
    a.e(alu_rm(Alu::Cmp, X16, st(offset_of!(DState, alloc_limit))));
    a.jcc(Cond::A, slow);
    a.e(load(X17, st(offset_of!(DState, words))));
    a.e(lea(X11, mi(X17, X14, 8, 0)));
    a.imm(X17, fixpt_heap::value::make_header(fixpt_heap::ObjType::Flonum as u8, 0, 8));
    a.e(store(m(X11, 0), X17));
    a.e(store(m(X11, 8), X9));
    a.e(store(m(X13, 0), X16));
    a.e(lea(RESULT, m(X11, 8 + fixpt_heap::value::TAG_BLOBLET as i32)));
}

/// `REGr`'s value unboxed to `rep`, in place.
fn unbox_to(a: &mut Asm, callouts: &mut Vec<Callout>, r: usize, rep: Rep) {
    in_place(a, r, |a, x| match rep {
        Rep::F64 => unbox_f64(a, x),
        _ => unbox_reg(a, callouts, x),
    });
}

/// The conversions `reps` asks for before an instruction; a test for a
/// fixnum going to `general` where it fails. `result` is where `RESULT`'s
/// value is (`src`).
fn convert(a: &mut Asm, callouts: &mut Vec<Callout>, cs: &[Convert], general: Label, result: Reg) {
    for c in cs {
        match *c {
            Convert::Box { r, rep: Rep::Raw { signed } } => in_place(a, r, |a, x| box_reg(a, callouts, x, signed)),
            Convert::Box { r, .. } => in_place(a, r, |a, x| box_f64(a, callouts, x)),
            Convert::Unbox { r, rep } => unbox_to(a, callouts, r, rep),
            Convert::Check { r: 0 } => check_reg(a, result, general),
            Convert::Check { r } => check_fixnum(a, r, general),
        }
    }
}

/// `int->f64` (primitive `p`) of the int in `RESULT`, raw into `RESULT`: a
/// fixnum's by `cvtsi2sd`, correctly rounded; a bignum's by the primitive.
fn f64_of_int(a: &mut Asm, callouts: &mut Vec<Callout>, p: usize) {
    let (slow, done) = (a.label(), a.label());
    a.e(test_imm(RESULT, 7));
    a.jcc(Cond::Ne, slow);
    a.e(mov(X13, RESULT));
    a.e(sar_imm(X13, 3));
    a.e(cvtsi2sd(0, X13));
    a.e(movq_from_xmm(RESULT, 0));
    a.jmp(done);
    a.bind(slow);
    pure_call(a, callouts, Callout::Pure { p, n: 1 }, &[RESULT], RESULT);
    unbox_f64(a, RESULT);
    a.bind(done);
}

/// `f64->int` (primitive `p`) of the raw `f64` in `RESULT`, into `RESULT`:
/// by `cvttsd2si` where that is exact and a fixnum; else the primitive's,
/// on the boxed value.
fn int_of_f64(a: &mut Asm, callouts: &mut Vec<Callout>, stubs: &mut Vec<(Label, u32)>, p: usize) {
    let (slow, done) = (a.label(), a.label());
    a.e(movq_to_xmm(0, RESULT));
    a.e(cvttsd2si(X13, 0));
    a.e(cvtsi2sd(1, X13));
    a.e(ucomis(true, 0, 1));
    a.jcc(Cond::Ne, slow);
    a.jcc(Cond::P, slow);
    a.e(mov(X14, X13));
    a.e(shl_imm(X14, 3));
    a.e(mov(X15, X14));
    a.e(sar_imm(X15, 3));
    a.e(cmp(X15, X13));
    a.jcc(Cond::Ne, slow);
    a.e(mov(RESULT, X14));
    a.jmp(done);
    a.bind(slow);
    box_f64(a, callouts, RESULT);
    pure_call(a, callouts, Callout::Pure { p, n: 1 }, &[RESULT], RESULT);
    a.e(alu_mi(Alu::Cmp, st(offset_of!(DState, trap)), 0));
    let l = a.label();
    stubs.push((l, PRIM_FAILED));
    a.jcc(Cond::Ne, l);
    a.bind(done);
}

/// After `ucomis` of `RESULT`'s operand against `y`'s, as arm64's `fcmp`
/// conditions read it: the comparison `what` into `RESULT`, `#f` where
/// either is a NaN. `ucomis` sets CF, ZF and PF for unordered, so `<` and
/// `<=` compare the other way round, `a`bove and `a`bove-or-equal.
fn float_test(a: &mut Asm, double: bool, what: &str) -> bool {
    let (l, r, c) = match what {
        "<" => (1, 0, Cond::A),
        "<=" => (1, 0, Cond::Ae),
        ">" => (0, 1, Cond::A),
        ">=" => (0, 1, Cond::Ae),
        "=" => (0, 1, Cond::E),
        _ => return false,
    };
    a.e(ucomis(double, l, r));
    a.flag(c, X13);
    if what == "=" {
        a.imm(X13, Value::FALSE.raw());
        a.e(cmov(Cond::P, RESULT, X13));
    }
    true
}

/// An `f64` operation `what` (as `reps::raw_op` names it), on raw `RESULT`
/// and `y`, into `RESULT`: raw, or a comparison's boolean. By way of
/// `xmm0` and `xmm1`, which nothing else keeps anything in.
fn f64_fast(a: &mut Asm, what: &str, y: Reg) {
    a.e(movq_to_xmm(0, RESULT));
    a.e(movq_to_xmm(1, y));
    if float_test(a, true, what) {
        return;
    }
    match what {
        "+" => a.e(fop(true, Fop::Add, 0, 1)),
        "-" => a.e(fop(true, Fop::Sub, 0, 1)),
        "*" => a.e(fop(true, Fop::Mul, 0, 1)),
        "/" => a.e(fop(true, Fop::Div, 0, 1)),
        // The sign bit cleared, or flipped, in the bits themselves.
        "-abs" => {
            a.e(shl_imm(RESULT, 1));
            a.e(shr_imm(RESULT, 1));
            return;
        }
        "-neg" => {
            a.imm(X13, 1 << 63);
            a.e(xor(RESULT, X13));
            return;
        }
        "-sqrt" => a.e(fop(true, Fop::Sqrt, 0, 0)),
        "-floor" => a.e(round(true, 0, 0, 1)),
        "-ceiling" => a.e(round(true, 0, 0, 2)),
        "-truncate" => a.e(round(true, 0, 0, 3)),
        _ => a.e(round(true, 0, 0, 0)),
    }
    a.e(movq_from_xmm(RESULT, 0));
}

/// An `f32` operation `what` on the immediates in `RESULT` and `y`, into
/// `RESULT`: each unboxed by a shift into `xmm0` and `xmm1`, the result
/// boxed by a shift and the subtag's add. False for one the runtime does.
fn f32_fast(a: &mut Asm, what: &str, y: Reg) -> bool {
    let known = matches!(what, "<" | "<=" | ">" | ">=" | "=" | "+" | "-" | "*" | "/" | "-abs" | "-neg" | "-sqrt" | "-floor" | "-ceiling" | "-truncate" | "-round");
    if !known {
        return false;
    }
    a.e(mov(X13, RESULT));
    a.e(shr_imm(X13, 32));
    a.e(movd_to_xmm(0, X13));
    a.e(mov(X14, y));
    a.e(shr_imm(X14, 32));
    a.e(movd_to_xmm(1, X14));
    if float_test(a, false, what) {
        return true;
    }
    match what {
        "+" => a.e(fop(false, Fop::Add, 0, 1)),
        "-" => a.e(fop(false, Fop::Sub, 0, 1)),
        "*" => a.e(fop(false, Fop::Mul, 0, 1)),
        "/" => a.e(fop(false, Fop::Div, 0, 1)),
        "-sqrt" => a.e(fop(false, Fop::Sqrt, 0, 0)),
        "-floor" => a.e(round(false, 0, 0, 1)),
        "-ceiling" => a.e(round(false, 0, 0, 2)),
        "-truncate" => a.e(round(false, 0, 0, 3)),
        "-round" => a.e(round(false, 0, 0, 0)),
        _ => {}
    }
    a.e(movd_from_xmm(X13, 0));
    match what {
        "-abs" => {
            a.imm(X14, 0x7fff_ffff);
            a.e(and(X13, X14));
        }
        "-neg" => a.e(alu_imm(Alu::Xor, X13, i32::MIN)),
        _ => {}
    }
    // `xor` with `i32::MIN` sign-extends: the high half back to 0.
    a.e(shl_imm(X13, 32));
    a.e(lea(RESULT, m(X13, (Value::f32(0.0).raw() & 0xff) as i32)));
    true
}

/// `RESULT`, the fixnum of an integer, wrapped to a 32-bit type's range:
/// its bits 3 to 34 kept, sign-extended if the type is signed.
fn wrap32(a: &mut Asm, signed: bool) {
    a.e(shl_imm(RESULT, 29));
    a.e(if signed { sar_imm(RESULT, 29) } else { shr_imm(RESULT, 29) });
}

/// An `i64` (signed) or `u64` operation `what` on raw `RESULT` and `y`
/// (raw, or a shift's count, a fixnum), into `RESULT`: raw, or a
/// comparison's boolean. Its arithmetic wraps, as the machine's does;
/// division by zero traps, and the least `i64` by −1 is itself, as
/// arm64's `sdiv` has it. `y` is not `RESULT`, `RCX` or `RDX`.
fn raw_fast(a: &mut Asm, stubs: &mut Vec<(Label, u32)>, signed: bool, what: &str, y: Reg) {
    let x = RESULT;
    let compare = match (what, signed) {
        ("<", true) => Some(Cond::L),
        ("<=", true) => Some(Cond::Le),
        (">", true) => Some(Cond::G),
        (">=", true) => Some(Cond::Ge),
        ("<", false) => Some(Cond::B),
        ("<=", false) => Some(Cond::Be),
        (">", false) => Some(Cond::A),
        (">=", false) => Some(Cond::Ae),
        ("=", _) => Some(Cond::E),
        _ => None,
    };
    if let Some(c) = compare {
        a.e(cmp(x, y));
        a.flag(c, X13);
        return;
    }
    let divide = |a: &mut Asm, stubs: &mut Vec<(Label, u32)>, remainder: bool| {
        a.e(test(y, y));
        let l = a.label();
        stubs.push((l, super::DIVIDED_BY_ZERO));
        a.jcc(Cond::E, l);
        let done = a.label();
        if signed {
            let normal = a.label();
            a.e(cmp_imm(y, -1));
            a.jcc(Cond::Ne, normal);
            if remainder {
                a.imm(RESULT, 0);
            } else {
                a.e(neg(RESULT));
            }
            a.jmp(done);
            a.bind(normal);
            a.e(cqo());
            a.e(idiv(y));
        } else {
            a.imm(RDX, 0);
            a.e(div(y));
        }
        if remainder {
            a.e(mov(RESULT, RDX));
        }
        a.bind(done);
    };
    match what {
        "from" => {}
        "+" => a.e(add(RESULT, y)),
        "-" => a.e(sub(RESULT, y)),
        "*" => a.e(imul(RESULT, y)),
        "-and" => a.e(and(RESULT, y)),
        "-or" => a.e(or(RESULT, y)),
        "-xor" => a.e(xor(RESULT, y)),
        "-not" => a.e(not(RESULT)),
        "-quotient" => divide(a, stubs, false),
        "-remainder" => divide(a, stubs, true),
        // The count, a fixnum, modulo 64 (as `shl` and `sar` take `cl`).
        "-shl" | "-shr" => {
            a.e(mov(RCX, y));
            a.e(shr_imm(RCX, 3));
            a.e(shift_cl(
                match (what, signed) {
                    ("-shl", _) => Shift::Shl,
                    (_, true) => Shift::Sar,
                    _ => Shift::Shr,
                },
                RESULT,
            ));
        }
        _ => unreachable!("a 64-bit operation"),
    }
}

/// `out` := how many elements the flat array in `arr` has (untagged): its
/// suffix's bytes, from its header 28 bytes before its pointer, over its
/// elements' size, by its layout in field 2. Uses X11 and X16.
fn flat_count(a: &mut Asm, arr: Reg, out: Reg) {
    use fixpt_heap::layout::*;
    a.e(load(out, m(arr, -28)));
    a.e(shr_imm(out, 32));
    a.e(load(X16, fld(arr, 2)));
    a.e(shr_imm(X16, 3));
    let (wide, done) = (a.label(), a.label());
    for c in [FLAT_I64, FLAT_U64, FLAT_F64] {
        a.e(cmp_imm(X16, c as i32));
        a.jcc(Cond::E, wide);
    }
    a.e(shr_imm(out, 2));
    a.jmp(done);
    a.bind(wide);
    a.e(shr_imm(out, 3));
    a.bind(done);
}

/// Where a flat array's elements are, and element `index` (in `y`, a
/// value): X14 the index, X15 the suffix, X16 the layout, as a fixnum; to
/// `slow` unless the index is a fixnum in range.
fn flat_element(a: &mut Asm, arr: Reg, y: Reg, slow: Label) {
    a.e(test_imm(y, 7));
    a.jcc(Cond::Ne, slow);
    a.e(mov(X14, y));
    a.e(sar_imm(X14, 3));
    flat_count(a, arr, X13);
    a.e(cmp(X14, X13));
    a.jcc(Cond::Ae, slow);
    a.e(load(X16, fld(arr, 2)));
    a.e(lea(X15, m(arr, -(fixpt_heap::value::TAG_BLOBLET as i32))));
}

/// `flatarray-ref` of the flat array in `RESULT` at `y`, into `RESULT`, by
/// its layout, as `procedure`'s `flat_ref`.
fn flat_ref(a: &mut Asm, y: Reg, slow: Label) {
    use fixpt_heap::layout::*;
    let end = a.label();
    flat_element(a, RESULT, y, slow);
    let is = |a: &mut Asm, code: i64, not: Label| {
        a.e(cmp_imm(X16, (code << 3) as i32));
        a.jcc(Cond::Ne, not);
    };
    let (not_f64, not_f32, not_i32, not_u32) = (a.label(), a.label(), a.label(), a.label());
    is(a, FLAT_F64, not_f64);
    a.e(load(X9, mi(X15, X14, 8, 0)));
    box_bits(a, slow);
    a.jmp(end);
    a.bind(not_f64);
    is(a, FLAT_F32, not_f32);
    a.e(load32(X13, mi(X15, X14, 4, 0)));
    a.e(shl_imm(X13, 32));
    a.e(lea(RESULT, m(X13, (Value::f32(0.0).raw() & 0xff) as i32)));
    a.jmp(end);
    a.bind(not_f32);
    is(a, FLAT_I32, not_i32);
    a.e(load32s(X13, mi(X15, X14, 4, 0)));
    a.e(shl_imm(X13, 3));
    a.e(mov(RESULT, X13));
    a.jmp(end);
    a.bind(not_i32);
    is(a, FLAT_U32, not_u32);
    a.e(load32(X13, mi(X15, X14, 4, 0)));
    a.e(shl_imm(X13, 3));
    a.e(mov(RESULT, X13));
    a.jmp(end);
    // `i64` or `u64`: a fixnum where it fits one.
    a.bind(not_u32);
    a.e(load(X13, mi(X15, X14, 8, 0)));
    let unsigned = a.label();
    a.e(cmp_imm(X16, (FLAT_U64 << 3) as i32));
    a.jcc(Cond::E, unsigned);
    a.e(mov(X14, X13));
    a.e(shl_imm(X14, 3));
    a.e(mov(X15, X14));
    a.e(sar_imm(X15, 3));
    a.e(cmp(X15, X13));
    a.jcc(Cond::Ne, slow);
    a.e(mov(RESULT, X14));
    a.jmp(end);
    a.bind(unsigned);
    a.e(mov(X15, X13));
    a.e(shr_imm(X15, 60));
    a.jcc(Cond::Ne, slow);
    a.e(shl_imm(X13, 3));
    a.e(mov(RESULT, X13));
    a.bind(end);
}

/// Suffix ref `r` taken apart, as `procedure`'s `suffix_owner`: X15 its
/// offset, X11 where its owner's suffix starts, X12 the owner's header,
/// X13 the suffix's length, X16 the trailer's distance; to `slow` unless
/// it is one whose owner has a trailer and a header of one word. Uses X9
/// and X14.
fn suffix_owner(a: &mut Asm, r: Reg, slow: Label) {
    use fixpt_heap::layout::*;
    use fixpt_heap::value::{SUFFIX_OFFSET_SHIFT, SUFFIX_OWNER_BITS, TAG_SUFFIX_REF, TAG_TRAILER};
    a.e(mov(X16, r));
    a.e(and_imm(X16, 7));
    a.e(cmp_imm(X16, TAG_SUFFIX_REF as i32));
    a.jcc(Cond::Ne, slow);
    ubfx(a, X14, r, 3, SUFFIX_OWNER_BITS);
    a.e(mov(X15, r));
    a.e(shr_imm(X15, SUFFIX_OFFSET_SHIFT as u8));
    a.e(load(X9, st(offset_of!(DState, words))));
    a.e(lea(X11, mi(X9, X14, 8, 0)));
    // The trailer, the last field, says how far back the header is.
    a.e(load(X16, m(X11, -8)));
    a.e(mov(X9, X16));
    a.e(and_imm(X9, 7));
    a.e(cmp_imm(X9, TAG_TRAILER as i32));
    a.jcc(Cond::Ne, slow);
    ubfx(a, X16, X16, T_DISTANCE.lo, 32);
    a.e(mov(X9, X11));
    a.e(lea(X12, m(X16, 0)));
    a.e(shl_imm(X12, 3));
    a.e(sub(X9, X12));
    a.e(load(X12, m(X9, -8)));
    a.e(mov(X9, X12));
    a.e(shr_imm(X9, H_LARGE.lo as u8));
    a.e(test_imm(X9, 1));
    a.jcc(Cond::Ne, slow);
    a.e(mov(X13, X12));
    a.e(shr_imm(X13, H_BYTES.lo as u8));
}

/// The same, to `slow` unless its owner is a program's own bloblet or a
/// flat array whose suffix is not frozen.
fn suffix_writable(a: &mut Asm, r: Reg, slow: Label) {
    use fixpt_heap::layout::*;
    suffix_owner(a, r, slow);
    let owned = a.label();
    ubfx(a, X9, X12, H_KIND.lo, H_KIND.width);
    a.e(cmp_imm(X9, const { kind("bloblet") } as i32));
    a.jcc(Cond::E, owned);
    a.e(cmp_imm(X9, const { kind("flat-array") } as i32));
    a.jcc(Cond::Ne, slow);
    a.bind(owned);
    a.e(mov(X9, X12));
    a.e(shr_imm(X9, H_SUFFIX_FROZEN.lo as u8));
    a.e(test_imm(X9, 1));
    a.jcc(Cond::Ne, slow);
}

/// `blobref-set!` of the suffix ref in `RESULT`, a scalar of layout
/// `code`, to `v` (with `raw`, an `f64`'s bits): unit into `RESULT`.
fn suffix_store(a: &mut Asm, code: i64, v: Reg, raw: bool, slow: Label) {
    use fixpt_heap::layout::*;
    suffix_writable(a, RESULT, slow);
    a.e(lea(X9, m(X15, flat_size(code) as i32)));
    a.e(cmp(X9, X13));
    a.jcc(Cond::A, slow);
    a.e(add(X11, X15));
    match code {
        FLAT_F64 if raw => a.e(store(m(X11, 0), v)),
        FLAT_F64 => {
            a.e(load(X13, m(v, -(fixpt_heap::value::TAG_BLOBLET as i32))));
            a.e(store(m(X11, 0), X13));
        }
        FLAT_F32 => {
            a.e(mov(X13, v));
            a.e(shr_imm(X13, 32));
            a.e(store32(m(X11, 0), X13));
        }
        FLAT_I64 | FLAT_U64 => {
            a.e(test_imm(v, 7));
            a.jcc(Cond::Ne, slow);
            a.e(mov(X13, v));
            a.e(sar_imm(X13, 3));
            a.e(store(m(X11, 0), X13));
        }
        _ => {
            a.e(mov(X13, v));
            a.e(sar_imm(X13, 3));
            a.e(store32(m(X11, 0), X13));
        }
    }
    a.imm(RESULT, Value::UNIT.raw());
}

/// `blobref-index` of the suffix ref in `RESULT` at `i`, of layout `code`,
/// `n << 32 | size`, into `RESULT`.
fn blobref_index(a: &mut Asm, code: i64, i: Reg, slow: Label) {
    use fixpt_heap::value::SUFFIX_OFFSET_SHIFT;
    let (n, size) = (code >> 32, code & 0xffff_ffff);
    a.e(test_imm(i, 7));
    a.jcc(Cond::Ne, slow);
    suffix_owner(a, RESULT, slow);
    a.e(mov(X9, i));
    a.e(sar_imm(X9, 3));
    a.imm(X17, n as u64);
    a.e(cmp(X9, X17));
    a.jcc(Cond::Ae, slow);
    if size > 0 && size & (size - 1) == 0 {
        a.e(shl_imm(X9, size.trailing_zeros() as u8));
    } else {
        a.imm(X17, size as u64);
        a.e(imul(X9, X17));
    }
    a.e(lea(X16, mi(X15, X9, 1, 0)));
    a.e(cmp(X16, X13));
    a.jcc(Cond::Ae, slow);
    a.e(shl_imm(X9, SUFFIX_OFFSET_SHIFT as u8));
    a.e(add(RESULT, X9));
}

/// `blobref-variant!` of the suffix ref in `RESULT` to label `l`, of layout
/// `code`, as `procedure`'s `flat_variant`.
fn flat_variant(a: &mut Asm, code: i64, l: Reg, slow: Label) {
    use fixpt_heap::value::SUFFIX_OFFSET_SHIFT;
    let (w, p) = (code & 7, code >> 8);
    let numeric = code & 8 != 0;
    if numeric {
        a.e(test_imm(l, 7));
        a.jcc(Cond::Ne, slow);
        a.e(mov(X17, l));
        a.e(sar_imm(X17, 3));
    }
    suffix_writable(a, RESULT, slow);
    if !numeric {
        // Fields 2 to the trailer's distance (X16), the first that is `l`.
        let (look, found) = (a.label(), a.label());
        a.imm(X17, 2);
        a.bind(look);
        a.e(cmp(X17, X16));
        a.jcc(Cond::A, slow);
        a.e(mov(X9, X17));
        a.e(shl_imm(X9, 3));
        a.e(neg(X9));
        a.e(add(X9, X11));
        a.e(load(X9, m(X9, 0)));
        a.e(cmp(X9, l));
        a.jcc(Cond::E, found);
        a.e(add_imm(X17, 1));
        a.jmp(look);
        a.bind(found);
        a.e(sub_imm(X17, 2));
    }
    if w < 8 {
        a.e(mov(X9, X17));
        a.e(shr_imm(X9, (8 * w) as u8));
        a.jcc(Cond::Ne, slow);
    }
    a.imm(X9, p as u64);
    a.e(lea(X16, mi(X15, X9, 1, 0)));
    a.e(cmp(X16, X13));
    a.jcc(Cond::Ae, slow);
    a.e(add(X11, X15));
    a.e(match w {
        1 => store8(m(X11, 0), X17),
        2 => store16(m(X11, 0), X17),
        _ => store32(m(X11, 0), X17),
    });
    a.e(shl_imm(X9, SUFFIX_OFFSET_SHIFT as u8));
    a.e(add(RESULT, X9));
}

/// `blobref-at` of the bloblet in `RESULT` at byte `d` of its suffix, into
/// `RESULT`, as `procedure`'s `blobref_at`.
fn blobref_at(a: &mut Asm, d: i64, slow: Label) {
    use fixpt_heap::layout::*;
    use fixpt_heap::value::{SUFFIX_OFFSET_LIMIT, SUFFIX_OFFSET_SHIFT, SUFFIX_OWNER_BITS, TAG_BLOBLET, TAG_SUFFIX_REF, TAG_TRAILER};
    a.e(mov(X16, RESULT));
    a.e(and_imm(X16, 7));
    a.e(cmp_imm(X16, TAG_BLOBLET as i32));
    a.jcc(Cond::Ne, slow);
    a.e(lea(X11, m(RESULT, -(TAG_BLOBLET as i32))));
    a.e(load(X16, m(X11, -8)));
    a.e(mov(X9, X16));
    a.e(and_imm(X9, 7));
    a.e(cmp_imm(X9, TAG_TRAILER as i32));
    a.jcc(Cond::Ne, slow);
    ubfx(a, X16, X16, T_DISTANCE.lo, 32);
    a.e(mov(X9, X16));
    a.e(shl_imm(X9, 3));
    a.e(neg(X9));
    a.e(add(X9, X11));
    a.e(load(X12, m(X9, -8)));
    a.e(mov(X9, X12));
    a.e(shr_imm(X9, H_LARGE.lo as u8));
    a.e(test_imm(X9, 1));
    a.jcc(Cond::Ne, slow);
    a.e(mov(X13, X12));
    a.e(shr_imm(X13, H_BYTES.lo as u8));
    a.imm(X9, SUFFIX_OFFSET_LIMIT as u64);
    a.e(cmp(X13, X9));
    a.jcc(Cond::Ae, slow);
    a.imm(X9, d as u64);
    a.e(cmp(X9, X13));
    a.jcc(Cond::Ae, slow);
    // The owner, the suffix's word in the heap, where it fits its bits.
    a.e(alu_rm(Alu::Sub, X11, st(offset_of!(DState, words))));
    a.e(mov(X9, X11));
    a.e(shr_imm(X9, (3 + SUFFIX_OWNER_BITS) as u8));
    a.jcc(Cond::Ne, slow);
    a.imm(X9, ((d as u64) << SUFFIX_OFFSET_SHIFT) | TAG_SUFFIX_REF);
    a.e(mov(RESULT, X11));
    a.e(or(RESULT, X9));
}

/// Suffix ref `RESULT` moved `d` bytes along, into `RESULT`.
fn suffix_step(a: &mut Asm, d: i64, slow: Label) {
    use fixpt_heap::value::{SUFFIX_OFFSET_SHIFT, TAG_SUFFIX_REF};
    if d == 0 {
        a.e(mov(X16, RESULT));
        a.e(and_imm(X16, 7));
        a.e(cmp_imm(X16, TAG_SUFFIX_REF as i32));
        a.jcc(Cond::Ne, slow);
        return;
    }
    suffix_owner(a, RESULT, slow);
    a.imm(X9, d as u64);
    a.e(add(X9, X15));
    a.e(cmp(X9, X13));
    a.jcc(Cond::Ae, slow);
    a.imm(X9, (d as u64) << SUFFIX_OFFSET_SHIFT);
    a.e(add(RESULT, X9));
}

/// `blobref-index` (`%fx26-suffix-ref-index`) of the suffix ref in REG1,
/// at REG2, of the layout in REG3, into `RESULT`.
fn suffix_index(a: &mut Asm, slow: Label) {
    use fixpt_heap::value::SUFFIX_OFFSET_SHIFT;
    let (r1, r2, r3) = (IN_REGS[1], IN_REGS[2], IN_REGS[3]);
    a.e(test_imm(r2, 7));
    a.jcc(Cond::Ne, slow);
    suffix_owner(a, r1, slow);
    a.e(mov(X9, r2));
    a.e(sar_imm(X9, 3));
    a.e(mov(X17, r3));
    a.e(shr_imm(X17, 35));
    a.e(cmp(X9, X17));
    a.jcc(Cond::Ae, slow);
    ubfx(a, X17, r3, 3, 32);
    a.e(imul(X9, X17));
    a.e(lea(X16, mi(X15, X9, 1, 0)));
    a.e(cmp(X16, X13));
    a.jcc(Cond::Ae, slow);
    a.e(shl_imm(X9, SUFFIX_OFFSET_SHIFT as u8));
    a.e(lea(RESULT, mi(r1, X9, 1, 0)));
}

/// A flat sum's tag at the suffix ref in `RESULT`, into `RESULT`, of
/// layout `code`, as `procedure`'s `flat_tag`.
fn flat_tag(a: &mut Asm, code: i64, slow: Label) {
    let w = code & 7;
    suffix_owner(a, RESULT, slow);
    a.e(lea(X9, m(X15, w as i32)));
    a.e(cmp(X9, X13));
    a.jcc(Cond::A, slow);
    a.e(lea(X14, mi(X11, X15, 1, 0)));
    a.e(match w {
        1 => load8(X13, m(X14, 0)),
        2 => load16(X13, m(X14, 0)),
        _ => load32(X13, m(X14, 0)),
    });
    if code & 8 != 0 {
        a.e(shl_imm(X13, 3));
        a.e(mov(RESULT, X13));
        return;
    }
    a.e(add_imm(X13, 2));
    a.e(cmp(X13, X16));
    a.jcc(Cond::A, slow);
    a.e(shl_imm(X13, 3));
    a.e(neg(X13));
    a.e(add(X13, X11));
    a.e(load(RESULT, m(X13, 0)));
}

/// `blobref-get` of the suffix ref in `RESULT`, a scalar of layout `code`,
/// into `RESULT`, as `procedure`'s `suffix_get`.
fn suffix_get(a: &mut Asm, code: i64, raw: bool, slow: Label) {
    use fixpt_heap::layout::*;
    suffix_owner(a, RESULT, slow);
    a.e(lea(X9, m(X15, flat_size(code) as i32)));
    a.e(cmp(X9, X13));
    a.jcc(Cond::A, slow);
    a.e(add(X11, X15));
    match code {
        FLAT_F64 if raw => a.e(load(RESULT, m(X11, 0))),
        FLAT_F64 => {
            a.e(load(X9, m(X11, 0)));
            box_bits(a, slow);
        }
        FLAT_F32 => {
            a.e(load32(X13, m(X11, 0)));
            a.e(shl_imm(X13, 32));
            a.e(lea(RESULT, m(X13, (Value::f32(0.0).raw() & 0xff) as i32)));
        }
        FLAT_I32 => {
            a.e(load32s(X13, m(X11, 0)));
            a.e(shl_imm(X13, 3));
            a.e(mov(RESULT, X13));
        }
        FLAT_U32 => {
            a.e(load32(X13, m(X11, 0)));
            a.e(shl_imm(X13, 3));
            a.e(mov(RESULT, X13));
        }
        FLAT_I64 => {
            a.e(load(X13, m(X11, 0)));
            a.e(mov(X14, X13));
            a.e(shl_imm(X14, 3));
            a.e(mov(X15, X14));
            a.e(sar_imm(X15, 3));
            a.e(cmp(X15, X13));
            a.jcc(Cond::Ne, slow);
            a.e(mov(RESULT, X14));
        }
        _ => {
            a.e(load(X13, m(X11, 0)));
            a.e(mov(X15, X13));
            a.e(shr_imm(X15, 60));
            a.jcc(Cond::Ne, slow);
            a.e(shl_imm(X13, 3));
            a.e(mov(RESULT, X13));
        }
    }
}

/// Whether the fixnum layout code in `c` is a 64-bit one's, to `wide`.
fn wide_layout(a: &mut Asm, c: Reg, wide: Label) {
    use fixpt_heap::layout::*;
    for code in [FLAT_I64, FLAT_U64, FLAT_F64] {
        a.e(cmp_imm(c, (code << 3) as i32));
        a.jcc(Cond::E, wide);
    }
}

/// `blobref-set!` of the suffix ref in REG1, a scalar of the layout the
/// fixnum in REG2 says, to REG3, as `procedure`'s `suffix_set`.
fn suffix_set(a: &mut Asm, slow: Label, done: Label) {
    use fixpt_heap::layout::*;
    let (r1, c, v) = (IN_REGS[1], IN_REGS[2], IN_REGS[3]);
    suffix_writable(a, r1, slow);
    // The width: 8 for the 64-bit layouts, else 4.
    let (eight, sized) = (a.label(), a.label());
    a.imm(X9, 4);
    wide_layout(a, c, eight);
    a.jmp(sized);
    a.bind(eight);
    a.imm(X9, 8);
    a.bind(sized);
    a.e(add(X9, X15));
    a.e(cmp(X9, X13));
    a.jcc(Cond::A, slow);
    a.e(add(X11, X15));
    let is = |a: &mut Asm, code: i64, not: Label| {
        a.e(cmp_imm(c, (code << 3) as i32));
        a.jcc(Cond::Ne, not);
    };
    let (not_f64, not_f32, wide, stored) = (a.label(), a.label(), a.label(), a.label());
    is(a, FLAT_F64, not_f64);
    a.e(load(X13, m(v, -(fixpt_heap::value::TAG_BLOBLET as i32))));
    a.e(store(m(X11, 0), X13));
    a.jmp(stored);
    a.bind(not_f64);
    is(a, FLAT_F32, not_f32);
    a.e(mov(X13, v));
    a.e(shr_imm(X13, 32));
    a.e(store32(m(X11, 0), X13));
    a.jmp(stored);
    a.bind(not_f32);
    a.e(cmp_imm(c, (FLAT_I64 << 3) as i32));
    a.jcc(Cond::E, wide);
    a.e(cmp_imm(c, (FLAT_U64 << 3) as i32));
    a.jcc(Cond::E, wide);
    a.e(mov(X13, v));
    a.e(sar_imm(X13, 3));
    a.e(store32(m(X11, 0), X13));
    a.jmp(stored);
    a.bind(wide);
    a.e(test_imm(v, 7));
    a.jcc(Cond::Ne, slow);
    a.e(mov(X13, v));
    a.e(sar_imm(X13, 3));
    a.e(store(m(X11, 0), X13));
    a.bind(stored);
    a.imm(RESULT, Value::UNIT.raw());
    a.jmp(done);
}

/// `flatarray-set!` of the flat array in REG1 at REG2 to REG3, as
/// `procedure`'s `flat_set`; `raw`: the value is an `f64`'s bits.
fn flat_set(a: &mut Asm, slow: Label, done: Label, raw: bool) {
    use fixpt_heap::layout::*;
    let (r1, r2, v) = (IN_REGS[1], IN_REGS[2], IN_REGS[3]);
    let stored = a.label();
    flat_element(a, r1, r2, slow);
    let is = |a: &mut Asm, code: i64, not: Label| {
        a.e(cmp_imm(X16, (code << 3) as i32));
        a.jcc(Cond::Ne, not);
    };
    if raw {
        a.e(store(mi(X15, X14, 8, 0), v));
        a.imm(RESULT, Value::UNIT.raw());
        a.jmp(done);
        return;
    }
    let (not_f64, not_f32, wide) = (a.label(), a.label(), a.label());
    is(a, FLAT_F64, not_f64);
    a.e(load(X13, m(v, -(fixpt_heap::value::TAG_BLOBLET as i32))));
    a.e(store(mi(X15, X14, 8, 0), X13));
    a.jmp(stored);
    a.bind(not_f64);
    is(a, FLAT_F32, not_f32);
    a.e(mov(X13, v));
    a.e(shr_imm(X13, 32));
    a.e(store32(mi(X15, X14, 4, 0), X13));
    a.jmp(stored);
    a.bind(not_f32);
    a.e(cmp_imm(X16, (FLAT_I64 << 3) as i32));
    a.jcc(Cond::E, wide);
    a.e(cmp_imm(X16, (FLAT_U64 << 3) as i32));
    a.jcc(Cond::E, wide);
    a.e(mov(X13, v));
    a.e(sar_imm(X13, 3));
    a.e(store32(mi(X15, X14, 4, 0), X13));
    a.jmp(stored);
    a.bind(wide);
    a.e(test_imm(v, 7));
    a.jcc(Cond::Ne, slow);
    a.e(mov(X13, v));
    a.e(sar_imm(X13, 3));
    a.e(store(mi(X15, X14, 8, 0), X13));
    a.bind(stored);
    a.imm(RESULT, Value::UNIT.raw());
    a.jmp(done);
}

/// The rest of `pure_fast`, as `procedure`'s: `f32` operations, and the
/// 32-bit integers', each the fixnum of its value, so their arithmetic is
/// the fixnums' then wrapped.
fn narrow_fast(a: &mut Asm, name: &str, y: Reg, slow: Label) -> bool {
    let x = RESULT;
    let Some(rest) = name.strip_prefix("%fx26-") else { return false };
    if let Some(what) = rest.strip_prefix("f32") {
        return f32_fast(a, what, y);
    }
    let signed = |t: &str| match t {
        "i32" => Some(true),
        "u32" => Some(false),
        _ => None,
    };
    if let Some(s) = rest.strip_prefix("int->").and_then(signed) {
        a.e(test_imm(x, 7));
        a.jcc(Cond::Ne, slow);
        wrap32(a, s);
        return true;
    }
    let Some(s) = rest.get(..3).and_then(signed) else { return false };
    let compare = match &rest[3..] {
        "<" => Some(Cond::L),
        "<=" => Some(Cond::Le),
        ">" => Some(Cond::G),
        ">=" => Some(Cond::Ge),
        "=" => Some(Cond::E),
        _ => None,
    };
    if let Some(c) = compare {
        a.e(cmp(x, y));
        a.flag(c, X13);
        return true;
    }
    let nonzero = |a: &mut Asm| {
        a.e(test(y, y));
        a.jcc(Cond::E, slow);
    };
    match &rest[3..] {
        "->int" => {}
        "+" => {
            a.e(add(RESULT, y));
            wrap32(a, s);
        }
        "-" => {
            a.e(sub(RESULT, y));
            wrap32(a, s);
        }
        "*" => {
            a.e(mov(X13, y));
            a.e(sar_imm(X13, 3));
            a.e(imul(RESULT, X13));
            wrap32(a, s);
        }
        // The raw values' quotient is the quotient's value, their
        // remainder the remainder's raw value (`y` a multiple of 8, never
        // −1).
        "-quotient" => {
            nonzero(a);
            a.e(cqo());
            a.e(idiv(y));
            a.e(shl_imm(RESULT, 3));
            wrap32(a, s);
        }
        "-remainder" => {
            nonzero(a);
            a.e(cqo());
            a.e(idiv(y));
            a.e(mov(RESULT, RDX));
        }
        "-and" => a.e(and(RESULT, y)),
        "-or" => a.e(or(RESULT, y)),
        "-xor" => a.e(xor(RESULT, y)),
        "-not" => {
            a.e(neg(RESULT));
            a.e(sub_imm(RESULT, 8));
            wrap32(a, s);
        }
        // The count's low five bits.
        "-shl" | "-shr" => {
            a.e(test_imm(y, 7));
            a.jcc(Cond::Ne, slow);
            a.e(mov(RCX, y));
            a.e(shr_imm(RCX, 3));
            a.e(and_imm(RCX, 31));
            if &rest[3..] == "-shl" {
                a.e(shift_cl(Shift::Shl, RESULT));
                wrap32(a, s);
            } else {
                // An arithmetic or logical shift right, the tag's bits
                // cleared.
                a.e(shift_cl(if s { Shift::Sar } else { Shift::Shr }, RESULT));
                a.e(and_imm(RESULT, -8));
            }
        }
        _ => return false,
    }
    true
}
