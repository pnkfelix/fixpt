//! The hand-encoded machine on x86_64: `generate`, `routine_body` and
//! `assemble_word` of the parent module, routine for routine, for the
//! other instruction set. The same `State`, the same stacks and the same
//! call-outs; only the code differs. Kept as close to the arm64 one as the
//! two instruction sets allow, so that a change to one is easily made to
//! the other: the same routines in the same order, with the same names for
//! the same steps.
//!
//! What x86_64 changes:
//! - Fewer registers: the heap's base, always 0 since values became
//!   addresses (`PLAN.md`, "The queue"), has none, and the fuel lives in
//!   the state, counted down there (`sub qword [st + fuel], 1`). Every
//!   other register of the arm64 machine has one here, and so do its
//!   scratch registers:
//!
//!   | arm64 | x86_64 | role |
//!   |---|---|---|
//!   | x20 | r14 | `IP` |
//!   | x21 | r13 | `CUR` |
//!   | x22 | r12 | `DSP` |
//!   | x23 | rbx | `RSP`, the return stack |
//!   | x24 | r15 | `ST` |
//!   | x25 | r10 | `TABLE` |
//!   | x26 | rbp | `FP` |
//!   | x27 | r9  | `CLO` |
//!   | x9, x10, x11 | rax, rdi, rsi | `W`, `X10`, `X11` |
//!   | x13, x14, x15, x16 | rcx, rdx, r8, r11 | `X13` … `X16` |
//!
//!   Only `ST` must survive a call into Rust, and it is callee-saved; the
//!   rest are saved in the state and loaded again, as on arm64.
//! - No link register, and no register code (`regcode`) yet.
//! - Variable-length instructions: code and offsets are in bytes, and every
//!   branch to a label is a 32-bit one, so none is ever out of reach (the
//!   arm64 machine's `long_branches` has no counterpart). A jump to the
//!   very next instruction is dropped.

use super::State;
use crate::x86_64::*;
use fixpt_engine::cellular::{MARK_MARK, PROMPT_MARK, Trap};
use fixpt_heap::layout::cellular::{CLOSURE_FREE0, CLOSURE_WORD, KIND, PRIMITIVES, ROUTINES, WORD_CELL0, WORD_ENTRY};
use fixpt_heap::layout::kind;
use fixpt_heap::value::{TAG_BLOBLET, TAG_PAIR, TAG_TRAILER};
use fixpt_heap::{Heap, Value};
use std::mem::offset_of;

const IP: Reg = R14;
const CUR: Reg = R13;
const DSP: Reg = R12;
const RSP: Reg = RBX;
const ST: Reg = R15;
const TABLE: Reg = R10;
/// The frame pointer: the address of the running closure's slot 0.
const FP: Reg = RBP;
/// The closure running.
const CLO: Reg = R9;
// Scratch, named for the arm64 registers they stand for.
const W: Reg = RAX;
const X10: Reg = RDI;
const X11: Reg = RSI;
const X13: Reg = RCX;
const X14: Reg = RDX;
const X15: Reg = R8;
const X16: Reg = R11;

/// A field of the state, as an operand.
fn st(f: usize) -> Mem {
    m(ST, f as i32)
}

/// Field `k` of the bloblet whose `suffix + 4` is in `reg`.
fn field(reg: Reg, k: usize) -> Mem {
    m(reg, -(4 + 8 * k as i32))
}

#[derive(Copy, Clone)]
struct Label(usize);

/// Instructions with labels, patched when everything is placed.
struct Asm {
    code: Vec<u8>,
    /// Where each label is, in bytes from this code's start.
    labels: Vec<Option<usize>>,
    /// Each 32-bit displacement to patch: where it is, and its label.
    fixups: Vec<(usize, usize)>,
    /// The last instruction, if it is a jump to a label: where it starts.
    last_jump: Option<usize>,
    /// Traps raised in the routine being emitted, placed after it.
    stubs: Vec<(Label, u64, u64)>,
    trap_common: Label,
    exit_common: Label,
    /// Compiling a word: where its next cell's code is, and a branch's
    /// target's, with the target's cell. `None` in the machine's own
    /// routines, which `NEXT`.
    cont: Option<Label>,
    target: Option<(Label, usize)>,
    /// Compiling a word: the cell being compiled.
    at: usize,
}

impl Asm {
    fn new() -> Asm {
        let mut a = Asm {
            code: Vec::new(),
            labels: Vec::new(),
            fixups: Vec::new(),
            last_jump: None,
            stubs: Vec::new(),
            trap_common: Label(0),
            exit_common: Label(0),
            cont: None,
            target: None,
            at: 0,
        };
        a.trap_common = a.label();
        a.exit_common = a.label();
        a
    }
    fn here(&self) -> usize {
        self.code.len()
    }
    fn e(&mut self, i: Ins) {
        self.code.extend_from_slice(&i);
        self.last_jump = None;
    }
    fn label(&mut self) -> Label {
        self.labels.push(None);
        Label(self.labels.len() - 1)
    }
    fn bind(&mut self, l: Label) {
        assert!(self.labels[l.0].is_none());
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
    /// A branch to `l`, its 32-bit displacement the last four bytes of `i`.
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
    /// Trap with `trap` if `c` holds.
    fn trap_if(&mut self, c: Cond, trap: Trap) {
        let (code, aux) = trap.code();
        let l = self.label();
        self.jcc(c, l);
        self.stubs.push((l, code, aux));
    }
    fn flush_stubs(&mut self) {
        for (l, code, aux) in std::mem::take(&mut self.stubs) {
            self.bind(l);
            self.trap(code, aux);
        }
    }
    /// To the common trap with `code` and `aux`.
    fn trap(&mut self, code: u64, aux: u64) {
        self.e(mov_imm(X13, code));
        self.e(mov_imm(X14, aux));
        let t = self.trap_common;
        self.jmp(t);
    }
    fn finish(mut self) -> Vec<u8> {
        for (at, l) in std::mem::take(&mut self.fixups) {
            let to = self.labels[l].expect("label never bound");
            let d = to as i64 - (at as i64 + 4);
            self.code[at..at + 4].copy_from_slice(&i32::try_from(d).expect("in reach").to_le_bytes());
        }
        self.code
    }
    /// No-ops up to a multiple of `n` bytes.
    fn align(&mut self, n: usize) {
        let pad = self.here().next_multiple_of(n) - self.here();
        self.code.extend_from_slice(&nops(pad));
        self.last_jump = None;
    }

    // --------------------------------------------------- machine sequences

    /// Dispatch on the word in `W`: the tail of `NEXT`, and how a word
    /// given to `execute` or to the machine is run. Leaves the word in
    /// `X11` too, where `docol` takes it.
    fn run_word_in_w(&mut self) {
        self.e(mov(X11, W));
        self.e(load(X10, field(W, WORD_ENTRY)));
        self.e(jmp_m(mi(TABLE, X10, 1, 0)));
    }

    /// On to the next cell of this word: `NEXT`, or, in a word compiled to
    /// machine code, a jump to that cell's code.
    fn cont(&mut self) {
        match self.cont {
            Some(l) => self.jmp(l),
            None => self.next(),
        }
    }

    /// On from where `CUR` and the ip now are, `d` (8k) in `dreg`: into the
    /// word's machine code there, if it has some, else `NEXT`.
    fn enter_cur(&mut self, dreg: Reg) {
        let cellular = self.label();
        self.e(load(X10, field(CUR, WORD_ENTRY)));
        self.e(test(X10, X10));
        self.jcc(Cond::E, cellular);
        self.e(load(X16, st(offset_of!(State, resume))));
        self.e(load(X16, mi(X16, X10, 1, 0)));
        self.e(test(X16, X16));
        self.jcc(Cond::E, cellular);
        self.e(load(X16, mi(X16, dreg, 1, 0)));
        self.e(test(X16, X16));
        self.jcc(Cond::E, cellular);
        self.e(jmp_r(X16));
        self.bind(cellular);
        self.next();
    }

    fn next(&mut self) {
        let word = self.label();
        self.e(load(W, m(IP, 0)));
        self.e(sub_imm(IP, 8));
        self.e(test_imm(W, 7));
        self.jcc(Cond::Ne, word);
        self.e(jmp_m(mi(TABLE, W, 1, 0)));
        self.bind(word);
        self.run_word_in_w();
    }

    /// Store the machine's registers into the state, the ip as `8k`.
    fn save(&mut self) {
        self.e(store(st(offset_of!(State, cur)), CUR));
        self.e(lea(X13, m(CUR, -4)));
        self.e(sub(X13, IP));
        self.e(store(st(offset_of!(State, d)), X13));
        self.e(store(st(offset_of!(State, dsp)), DSP));
        self.e(store(st(offset_of!(State, rsp)), RSP));
        self.fp_encode(X13);
        self.e(store(st(offset_of!(State, fp)), X13));
        self.e(store(st(offset_of!(State, clo)), CLO));
    }

    /// `reg` = the frame pointer as a return entry keeps it:
    /// `ds_base - 8 - FP`, the bits of its fixnum index.
    fn fp_encode(&mut self, reg: Reg) {
        self.e(load(reg, st(offset_of!(State, ds_base))));
        self.e(sub_imm(reg, 8));
        self.e(sub(reg, FP));
    }

    /// `FP` from an encoded frame pointer in `reg`.
    fn fp_decode(&mut self, reg: Reg) {
        self.e(load(FP, st(offset_of!(State, ds_base))));
        self.e(sub_imm(FP, 8));
        self.e(sub(FP, reg));
    }

    /// Compare `reg` with a constant Value (`X16` may be used for it).
    fn cmp_value(&mut self, reg: Reg, v: Value) {
        match i32::try_from(v.raw() as i64) {
            Ok(imm) => self.e(cmp_imm(reg, imm)),
            Err(_) => {
                self.e(mov_imm(X16, v.raw()));
                self.e(cmp(reg, X16));
            }
        }
    }

    /// `reg` = `#t` if `c` holds after the comparison just made, else `#f`.
    fn boolean(&mut self, reg: Reg, c: Cond) {
        self.e(load(reg, st(offset_of!(State, fal))));
        self.e(cmov_m(c, reg, st(offset_of!(State, tru))));
    }

    /// Push `reg` on the data stack.
    fn push_ds(&mut self, reg: Reg) {
        self.e(sub_imm(DSP, 8));
        self.e(store(m(DSP, 0), reg));
    }

    /// Pop the data stack into `reg`.
    fn pop_ds(&mut self, reg: Reg) {
        self.e(load(reg, m(DSP, 0)));
        self.e(add_imm(DSP, 8));
    }

    /// The next cell, an operand, into `reg`.
    fn operand(&mut self, reg: Reg) {
        self.e(load(reg, m(IP, 0)));
        self.e(sub_imm(IP, 8));
    }

    /// A taken branch's new ip. In a compiled word it is made from the
    /// word, not from the ip, so that a loop's iterations do not wait on
    /// one chain of ip updates through them all.
    fn branch_ip(&mut self) {
        match self.target {
            Some((_, to)) => self.e(lea(IP, m(CUR, -((4 + 8 * (WORD_CELL0 + to)) as i32)))),
            None => self.e(sub(IP, X13)),
        }
    }

    /// Push a return entry, `(CUR, 8k, fp, CLO)`, from this word as it
    /// stands: the ip already past what this routine consumed.
    fn push_return(&mut self) {
        self.e(lea(X13, m(CUR, -4)));
        self.e(sub(X13, IP));
        self.fp_encode(X14);
        self.e(sub_imm(RSP, 32));
        self.e(store(m(RSP, 0), CUR));
        self.e(store(m(RSP, 8), X13));
        self.e(store(m(RSP, 16), X14));
        self.e(store(m(RSP, 24), CLO));
    }

    /// Pop a return entry and return to it, or leave the machine at the
    /// bottom one (whose word is `#f`). Prompts' and marks' entries are
    /// not returns: pass them by.
    fn pop_return(&mut self) {
        let again = self.label();
        self.bind(again);
        self.e(load(X13, m(RSP, 0)));
        for mark in [PROMPT_MARK, MARK_MARK] {
            let not = self.label();
            self.cmp_value(X13, mark);
            self.jcc(Cond::Ne, not);
            self.e(add_imm(RSP, 32));
            self.jmp(again);
            self.bind(not);
        }
        self.e(load(CUR, m(RSP, 0)));
        self.e(load(X13, m(RSP, 8)));
        self.e(load(X14, m(RSP, 16)));
        self.e(load(CLO, m(RSP, 24)));
        self.e(add_imm(RSP, 32));
        self.cmp_value(CUR, Value::FALSE);
        let ec = self.exit_common;
        self.jcc(Cond::E, ec);
        self.e(lea(IP, m(CUR, -4)));
        self.e(sub(IP, X13));
        self.fp_decode(X14);
        self.enter_cur(X13);
    }

    /// Check that `reg` is a cellular closure, else go to `not`: its
    /// trailer says F, and its header, F + 1 words back, its kind. Leaves
    /// it in `X11` and its trailer in `X15`.
    fn is_closure(&mut self, reg: Reg, not: Label) {
        self.e(mov(X13, reg));
        self.e(and_imm(X13, 7));
        self.e(cmp_imm(X13, TAG_BLOBLET as i32));
        self.jcc(Cond::Ne, not);
        self.e(mov(X11, reg));
        self.e(load(X15, field(X11, 1)));
        self.e(mov(X13, X15));
        self.e(and_imm(X13, 7));
        self.e(cmp_imm(X13, TAG_TRAILER as i32));
        self.jcc(Cond::Ne, not);
        self.header_kind(X14, X11, X15);
        self.e(cmp_imm(X14, const { kind("cellular-closure") } as i32));
        self.jcc(Cond::Ne, not);
    }

    /// `d` = the kind in the header of the bloblet in `obj` (its `suffix +
    /// 4`), whose trailer is in `trailer`: the header is F + 1 words before
    /// the suffix, and the trailer is F << 3 | 5, so header = obj - 4 - 8 -
    /// 8F, and its kind bits 3 to 10.
    fn header_kind(&mut self, d: Reg, obj: Reg, trailer: Reg) {
        self.e(mov(d, obj));
        self.e(sub(d, trailer));
        self.e(load(d, m(d, -7)));
        self.e(shr_imm(d, 3));
        self.e(and_imm(d, 0xff));
    }

    /// Load them back, recomputing the ip from `cur` and `d`, which is left
    /// in `X13`.
    fn load(&mut self) {
        self.e(load(CUR, st(offset_of!(State, cur))));
        self.e(load(X13, st(offset_of!(State, d))));
        self.e(lea(IP, m(CUR, -4)));
        self.e(sub(IP, X13));
        self.e(load(DSP, st(offset_of!(State, dsp))));
        self.e(load(RSP, st(offset_of!(State, rsp))));
        self.e(load(TABLE, st(offset_of!(State, table))));
        self.e(load(CLO, st(offset_of!(State, clo))));
        self.e(load(X14, st(offset_of!(State, fp))));
        self.fp_decode(X14);
    }

    fn fuel(&mut self) {
        self.e(alu_mi(Alu::Sub, st(offset_of!(State, fuel)), 1));
        self.trap_if(Cond::E, Trap::OutOfFuel);
    }

    /// A taken branch's poll: only a backward one can make a loop, so a
    /// branch known to go forward (in a compiled word) makes none.
    fn fuel_unless_forward(&mut self) {
        if !matches!(self.target, Some((_, to)) if to > self.at) {
            self.fuel();
        }
    }

    fn ds_limit(&mut self) {
        self.e(alu_rm(Alu::Cmp, DSP, st(offset_of!(State, ds_limit))));
        self.trap_if(Cond::B, Trap::StackOverflow);
    }

    fn rs_limit(&mut self) {
        self.e(alu_rm(Alu::Cmp, RSP, st(offset_of!(State, rs_limit))));
        self.trap_if(Cond::Be, Trap::TooDeep);
    }

    /// Leave machine code for the Rust side of routine `n`; carry on
    /// unless it reports a trap: with this word's next cell if the routine
    /// only computes, or from wherever it left the machine (control).
    fn callout(&mut self, n: u64) {
        self.save();
        self.e(mov(RDI, ST));
        self.e(mov_imm(RSI, n));
        self.e(call_m(st(offset_of!(State, callout))));
        self.e(test(RAX, RAX));
        let exit = self.exit_common;
        self.jcc(Cond::Ne, exit);
        self.load();
        if super::CONTROL_CALLOUTS.contains(&ROUTINES[n as usize].0) {
            self.enter_cur(X13);
        } else {
            self.cont();
        }
    }

    /// `X13` = top, `X14` = the one below; trap unless both are fixnums.
    fn two_fixnums(&mut self, name: &'static str) {
        self.both_fixnums();
        self.trap_if(Cond::Ne, Trap::Type { routine: name });
    }

    /// `X13` = top, `X14` = the one below; `ne` unless both are fixnums.
    fn both_fixnums(&mut self) {
        self.e(load(X13, m(DSP, 0)));
        self.e(load(X14, m(DSP, 8)));
        self.e(mov(X15, X13));
        self.e(or(X15, X14));
        self.e(test_imm(X15, 7));
    }

    /// Trap with `trap` unless the tag of `reg` is `tag` (clobbers `X13`).
    fn check_tag(&mut self, reg: Reg, tag: u64, trap: Trap) {
        self.e(mov(X13, reg));
        self.e(and_imm(X13, 7));
        self.e(cmp_imm(X13, tag as i32));
        self.trap_if(Cond::Ne, trap);
    }
}

/// The whole machine: an entry routine, the common exits, and one routine
/// per routine number. Returns the code, where its entry is, where each
/// routine starts, and where the common trap and exit are, all in bytes.
pub(super) fn generate() -> (Vec<u8>, usize, Vec<usize>, [usize; 2]) {
    let mut a = Asm::new();

    // The entry, called from Rust with the state in rdi: the callee-saved
    // registers kept, and the stack 16-aligned for the calls into Rust.
    let entry = a.here();
    for r in [RBX, RBP, R12, R13, R14, R15] {
        a.e(push(r));
    }
    a.e(sub_imm(RSP_, 8));
    a.e(mov(ST, RDI));
    a.load();
    a.e(load(W, st(offset_of!(State, start))));
    a.run_word_in_w();

    // A trap: code in X13 and detail in X14; then the common exit.
    let (tc, ec) = (a.trap_common, a.exit_common);
    a.bind(tc);
    a.e(store(st(offset_of!(State, status)), X13));
    a.e(store(st(offset_of!(State, aux)), X14));
    a.bind(ec);
    a.save();
    a.e(add_imm(RSP_, 8));
    for r in [R15, R14, R13, R12, RBP, RBX] {
        a.e(pop(r));
    }
    a.e(ret());

    let mut starts = Vec::new();
    for (n, (name, _)) in ROUTINES.iter().enumerate() {
        a.align(16);
        starts.push(a.here());
        routine_body(&mut a, n, name);
        a.flush_stubs();
    }
    let commons = [a.trap_common, a.exit_common].map(|l| a.labels[l.0].expect("bound"));
    (a.finish(), entry, starts, commons)
}

/// The machine stack pointer, which the machine's registers never name
/// otherwise (`RSP` is the return stack's).
const RSP_: Reg = crate::x86_64::RSP;

/// Routine `n`'s code: in the machine, ending in `NEXT`; or, in a word
/// compiled to machine code (`a.cont` set), going on to the next cell's.
fn routine_body(a: &mut Asm, n: usize, name: &'static str) {
    match name {
        "docol" => {
            // W is the word and X11 its suffix + 4.
            a.fuel();
            a.ds_limit();
            a.rs_limit();
            a.push_return();
            a.e(mov(CUR, W));
            a.e(lea(IP, m(X11, -((4 + 8 * WORD_CELL0) as i32))));
            a.next();
        }
        "exit" => a.pop_return(),
        "halt" => {
            let ec = a.exit_common;
            a.jmp(ec);
        }
        "lit" => {
            a.operand(X13);
            a.push_ds(X13);
            a.cont();
        }
        "branch" => {
            if a.target.is_none() {
                a.operand(X13);
            }
            a.branch_ip();
            a.fuel_unless_forward();
            a.ds_limit();
            match a.target {
                Some((t, _)) => a.jmp(t),
                None => a.next(),
            }
        }
        "0branch" => {
            let skip = a.label();
            a.pop_ds(X14);
            a.operand(X13);
            a.cmp_value(X14, Value::FALSE);
            a.jcc(Cond::Ne, skip);
            a.branch_ip();
            a.fuel_unless_forward();
            a.ds_limit();
            match a.target {
                Some((t, _)) => {
                    a.jmp(t);
                    a.bind(skip);
                    a.cont();
                }
                None => {
                    a.bind(skip);
                    a.next();
                }
            }
        }
        "execute" => {
            let is_ref = a.label();
            let bad = a.label();
            a.pop_ds(W);
            a.e(test_imm(W, 7));
            a.jcc(Cond::Ne, is_ref);
            // A primitive, by number: 1 ≤ n < PRIMITIVES.
            a.e(test(W, W));
            a.jcc(Cond::E, bad);
            a.e(cmp_imm(W, (8 * PRIMITIVES) as i32));
            a.jcc(Cond::Ae, bad);
            a.e(jmp_m(mi(TABLE, W, 1, 0)));
            a.bind(bad);
            a.e(mov_imm(X13, Trap::NoRoutine(0).code().0));
            a.e(mov(X14, W));
            a.e(sar_imm(X14, 3));
            let tc = a.trap_common;
            a.jmp(tc);
            // A word: a bloblet with a trailer, whose header says its kind.
            a.bind(is_ref);
            a.check_tag(W, TAG_BLOBLET, Trap::NotAWord);
            a.e(mov(X11, W));
            a.e(load(X15, field(X11, 1)));
            a.check_tag(X15, TAG_TRAILER, Trap::NotAWord);
            a.header_kind(X14, X11, X15);
            a.e(cmp_imm(X14, KIND as i32));
            a.trap_if(Cond::Ne, Trap::NotAWord);
            a.run_word_in_w();
        }
        "dup" => {
            a.e(load(X13, m(DSP, 0)));
            a.push_ds(X13);
            a.cont();
        }
        "drop" => {
            a.e(add_imm(DSP, 8));
            a.cont();
        }
        "swap" => {
            a.e(load(X13, m(DSP, 0)));
            a.e(load(X14, m(DSP, 8)));
            a.e(store(m(DSP, 0), X14));
            a.e(store(m(DSP, 8), X13));
            a.cont();
        }
        "over" => {
            a.e(load(X13, m(DSP, 8)));
            a.push_ds(X13);
            a.cont();
        }
        "+" | "-" => {
            a.two_fixnums(name);
            a.e(mov(X15, X14));
            a.e(if name == "+" { add(X15, X13) } else { sub(X15, X13) });
            a.trap_if(Cond::O, Trap::Overflow { routine: name });
            a.e(add_imm(DSP, 8));
            a.e(store(m(DSP, 0), X15));
            a.cont();
        }
        "<" => {
            a.two_fixnums(name);
            a.e(cmp(X14, X13));
            a.boolean(X15, Cond::L);
            a.e(add_imm(DSP, 8));
            a.e(store(m(DSP, 0), X15));
            a.cont();
        }
        "eq" => {
            a.e(load(X13, m(DSP, 0)));
            a.e(load(X14, m(DSP, 8)));
            a.e(cmp(X14, X13));
            a.boolean(X15, Cond::E);
            a.e(add_imm(DSP, 8));
            a.e(store(m(DSP, 0), X15));
            a.cont();
        }
        // A list may be `nil`: `car` of it traps, as the Rust machine's does.
        "car" | "cdr" | "pair-car" | "pair-cdr" => {
            a.e(load(X15, m(DSP, 0)));
            a.check_tag(X15, TAG_PAIR, Trap::Type { routine: name });
            a.e(load(X15, m(X15, if name.ends_with("car") { -1 } else { 7 })));
            a.e(store(m(DSP, 0), X15));
            a.cont();
        }
        // Typed: the checker has proved the operands ints. Fixnums here; a
        // bignum, or a sum past a fixnum, the Rust machine's (PLAN.md, Q2).
        "int-add" | "int-sub" => {
            let slow = a.label();
            a.both_fixnums();
            a.jcc(Cond::Ne, slow);
            a.e(mov(X15, X14));
            a.e(if name == "int-add" { add(X15, X13) } else { sub(X15, X13) });
            a.jcc(Cond::O, slow);
            a.e(add_imm(DSP, 8));
            a.e(store(m(DSP, 0), X15));
            a.cont();
            a.bind(slow);
            a.callout(n as u64);
        }
        "int-less" | "int-eq" => {
            let slow = a.label();
            a.both_fixnums();
            a.jcc(Cond::Ne, slow);
            a.e(cmp(X14, X13));
            a.boolean(X15, if name == "int-less" { Cond::L } else { Cond::E });
            a.e(add_imm(DSP, 8));
            a.e(store(m(DSP, 0), X15));
            a.cont();
            a.bind(slow);
            a.callout(n as u64);
        }
        "field" => {
            // Field k is 8k bytes before the bloblet's suffix; X13 is 8k.
            a.operand(X13);
            a.e(load(X16, m(DSP, 0)));
            a.e(sub(X16, X13));
            a.e(load(X15, m(X16, -4)));
            a.e(store(m(DSP, 0), X15));
            a.cont();
        }
        "field@" => {
            // The fast path: a bloblet with a trailer, which says F.
            let slow = a.label();
            a.e(load(X15, m(DSP, 0)));
            a.e(load(X14, m(DSP, 8)));
            a.e(test_imm(X15, 7));
            a.trap_if(Cond::Ne, Trap::Type { routine: name });
            a.check_tag(X14, TAG_BLOBLET, Trap::Type { routine: name });
            a.e(load(X16, field(X14, 1)));
            a.e(mov(X13, X16));
            a.e(and_imm(X13, 7));
            a.e(cmp_imm(X13, TAG_TRAILER as i32));
            a.jcc(Cond::Ne, slow);
            // 2 ≤ k ≤ F; 8k is X15 and 8F is the trailer less its tag.
            a.e(cmp_imm(X15, 16));
            a.trap_if(Cond::L, Trap::Field { routine: name });
            a.e(sub_imm(X16, TAG_TRAILER as i32));
            a.e(cmp(X15, X16));
            a.trap_if(Cond::G, Trap::Field { routine: name });
            a.e(sub(X14, X15));
            a.e(load(X15, m(X14, -4)));
            a.e(add_imm(DSP, 8));
            a.e(store(m(DSP, 0), X15));
            a.cont();
            a.bind(slow);
            a.callout(n as u64);
        }
        // Code compiled from FX-26: frames on the data stack, flat
        // closures, globals, calls; as `fixpt_engine::cellular` has them.
        "slot" | "slot!" => {
            // Slot i is 8i bytes below FP, and must be on the stack.
            a.operand(X13);
            a.e(mov(X14, FP));
            a.e(sub(X14, X13));
            if name == "slot!" {
                a.pop_ds(X15);
            }
            a.e(cmp(X14, DSP));
            a.trap_if(Cond::B, Trap::Field { routine: name });
            if name == "slot" {
                a.e(load(X15, m(X14, 0)));
                a.push_ds(X15);
            } else {
                a.e(store(m(X14, 0), X15));
            }
            a.cont();
        }
        "free" => {
            // Field CLOSURE_FREE0 + i of the closure running, if it has it.
            let bad = a.label();
            a.operand(X10);
            a.is_closure(CLO, bad);
            a.e(add_imm(X10, (8 * CLOSURE_FREE0) as i32));
            a.e(mov(X16, X15));
            a.e(sub_imm(X16, TAG_TRAILER as i32));
            a.e(cmp(X10, X16));
            a.jcc(Cond::G, bad);
            a.e(mov(X14, X11));
            a.e(sub(X14, X10));
            a.e(load(X15, m(X14, -4)));
            a.push_ds(X15);
            a.cont();
            a.bind(bad);
            let (code, aux) = Trap::Field { routine: name }.code();
            a.trap(code, aux);
        }
        "global" | "global!" => {
            // The cell's value is its field 2 (checked when the word was
            // made).
            a.operand(X11);
            if name == "global" {
                a.e(load(X15, field(X11, 2)));
                a.push_ds(X15);
            } else {
                a.pop_ds(X15);
                a.e(store(field(X11, 2), X15));
                // One more write, for the guards (`global-guard`).
                a.e(alu_mi(Alu::Add, field(X11, fixpt_heap::layout::cellular::GLOBAL_WRITES), Value::fixnum(1).raw() as i32));
                let mark = card_mark(X11, -(4 + 8 * 2), ST, offset_of!(State, cards) as i32, X13, X16);
                a.code.extend_from_slice(&mark);
                a.last_jump = None;
            }
            a.cont();
        }
        "call" | "tailcall" | "tcall" | "ttailcall" => {
            // A cellular closure on top: its word, over a frame of the n
            // values below it. Anything else (a continuation, or not a
            // procedure) goes the Rust machine's way. A typed call's callee
            // is a closure (the checker says so), so it is not tested; and
            // a tail call grows neither stack, so a typed one does not
            // check them either.
            let typed = matches!(name, "tcall" | "ttailcall");
            let name = if typed { &name[1..] } else { name };
            let other = a.label();
            a.e(load(W, m(DSP, 0)));
            if !typed {
                a.is_closure(W, other);
            }
            a.fuel();
            if !(typed && name == "tailcall") {
                a.ds_limit();
                a.rs_limit();
            }
            // The count, 8n, in X10: `push_return` uses X13 and X14.
            a.operand(X10);
            a.e(add_imm(DSP, 8));
            if name == "call" {
                a.push_return();
                // Slot 0 is the first argument, the deepest: DSP + 8n - 8.
                a.e(lea(FP, mi(DSP, X10, 1, -8)));
            } else {
                // Slide the n arguments down over this frame, deepest
                // first; FP stays.
                let (top, done) = (a.label(), a.label());
                a.e(lea(X14, mi(DSP, X10, 1, -8)));
                a.e(mov(X15, FP));
                a.e(mov(X16, X10));
                a.bind(top);
                a.e(test(X16, X16));
                a.jcc(Cond::E, done);
                a.e(load(X10, m(X14, 0)));
                a.e(sub_imm(X14, 8));
                a.e(store(m(X15, 0), X10));
                a.e(sub_imm(X15, 8));
                a.e(sub_imm(X16, 8));
                a.jmp(top);
                a.bind(done);
                a.e(lea(DSP, m(X15, 8)));
            }
            a.e(mov(CLO, W));
            a.e(load(CUR, field(W, CLOSURE_WORD)));
            a.e(lea(IP, m(CUR, -((4 + 8 * WORD_CELL0) as i32))));
            a.e(mov_imm(X13, (8 * WORD_CELL0) as u64));
            a.enter_cur(X13);
            a.bind(other);
            if !typed {
                a.callout(n as u64);
            }
        }
        "return" => {
            // The value on top replaces the frame; then back.
            a.pop_ds(X15);
            a.e(lea(X14, m(FP, 8)));
            a.e(cmp(DSP, X14));
            a.trap_if(Cond::A, Trap::Underflow { routine: name });
            a.e(mov(DSP, FP));
            a.e(store(m(DSP, 0), X15));
            a.pop_return();
        }
        // Everything else: the Rust machine runs it on these stacks
        // (`callout`), so it means exactly what it means there.
        _ => a.callout(n as u64),
    }
}

/// A word's cells as machine code, `assemble_word`'s x86_64 form: the
/// code, and where each cell's code starts, in bytes, or -1 for a cell
/// that is an operand.
pub fn assemble_word(heap: &Heap, word: Value) -> Result<(Vec<u8>, Vec<i64>), String> {
    let fields = heap.bloblet_head(word).fields;
    let cells: Vec<Value> = (WORD_CELL0..=fields).map(|k| heap.bloblet_slot(word, k)).collect();
    // Where each instruction starts.
    let mut starts = vec![false; cells.len() + 1];
    let mut i = 0;
    while i < cells.len() {
        starts[i] = true;
        i += if cells[i].is_fixnum() { 1 + fixpt_heap::layout::cellular::operands(ROUTINES[cells[i].as_fixnum() as usize].0) } else { 1 };
    }
    let mut a = Asm::new();
    let labels: Vec<Label> = (0..=cells.len()).map(|_| a.label()).collect();
    // As a cell: `docol`'s work, then the first cell.
    a.fuel();
    a.ds_limit();
    a.rs_limit();
    a.push_return();
    a.e(mov(CUR, W));
    a.e(lea(IP, m(X11, -((4 + 8 * WORD_CELL0) as i32))));
    a.jmp(labels[0]);
    for (i, cell) in cells.iter().enumerate() {
        if !starts[i] {
            continue;
        }
        a.bind(labels[i]);
        if cell.is_fixnum() {
            let n = cell.as_fixnum() as usize;
            let name = ROUTINES.get(n).ok_or("no such routine")?.0;
            let next = (i + 1..=cells.len()).find(|&j| starts[j] || j == cells.len()).expect("the end");
            a.cont = (next < cells.len()).then_some(labels[next]);
            a.target = if matches!(name, "branch" | "0branch") {
                let to = (i + 1) as i64 + 1 + cells[i + 1].as_fixnum();
                Some((labels[to as usize], to as usize))
            } else {
                None
            };
            a.at = i;
            // The cell is consumed, as `NEXT` would have.
            a.e(sub_imm(IP, 8));
            routine_body(&mut a, n, name);
        } else {
            a.cont = None;
            a.target = None;
            a.operand(W);
            a.run_word_in_w();
        }
    }
    // The traps, after all the cells, so that each cell's code runs on
    // into the next's.
    a.flush_stubs();
    // The machine's common trap and exit, through the state: no branch
    // leaves this code, so it may be placed anywhere, and run by any
    // machine.
    let [tc, ec] = [a.trap_common, a.exit_common];
    a.bind(tc);
    a.e(jmp_m(st(offset_of!(State, trap))));
    a.bind(ec);
    a.e(jmp_m(st(offset_of!(State, exit))));
    let at: Vec<i64> = (0..cells.len()).map(|i| if starts[i] { a.labels[labels[i].0].expect("bound") as i64 } else { -1 }).collect();
    Ok((a.finish(), at))
}
