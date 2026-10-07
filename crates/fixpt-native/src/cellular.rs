//! The native inner interpreter: the same cellular words the Rust bootstrap
//! interpreter runs (`fixpt_engine::cellular`), run by machine code written
//! into a code space with our own encoder.
//!
//! **Invariant: a word's code is position-independent.** It refers to
//! nothing outside itself by address: it reaches the machine's trap and
//! exit through the state (`ldr x16, [st, #trap]; br x16`), other words
//! through the table (`table[slot]`), and every branch it has stays inside
//! it; a saved ip is a cell's index, not an address. The only absolute
//! addresses of a word's code are outside it, where a move can rewrite
//! them: its slot's entry in the table, its table of where to resume, and
//! `CODE_OF_SLOT`. So code is moved by copying it, as collecting the code
//! does ([`NativeMachine::collect_code`]). The `far` that
//! [`assemble_word`] and [`assemble_register_word`] take is vestigial.
//! Keep any code generated here the same: an address it needs goes in a
//! table a move rewrites.
//!
//! One routine per routine number, each ending in its own copy of `NEXT`:
//!
//! ```text
//! NEXT:  ldr  x9, [ip], #-8      ; the cell; cells run toward higher k
//!        tst  x9, #7             ; a fixnum names a primitive
//!        b.ne 1f
//!        ldr  x10, [table, x9]   ; n<<3 is already the byte offset
//!        br   x10
//!    1:  add  x11, base, x9      ; a word: suffix + 4
//!        ldur x10, [x11, #-20]   ; its entry, a fixnum routine number
//!        ldr  x10, [table, x10]
//!        br   x10
//! ```
//!
//! The machine keeps its registers across routines, and saves them in a
//! [`State`] whenever it leaves machine code: to return, or to call into Rust
//! for what allocates (`cons`) or is rare (`field!`, and `field@` on a
//! bloblet with no trailer). There the Rust side sees both stacks as slices
//! of Values, the roots they are, and may collect. Afterwards the machine
//! reloads everything, the heap's base included, since a collection moves it.
//!
//! The ip is kept as an address while running and as the fixnum `k` of the
//! next cell (`8k` bytes before the current word's suffix, which is the same
//! bits) whenever it is saved, so it survives the word moving.
//!
//! What the machine checks, and where: types and overflow in every primitive;
//! fuel and stack limits where a word is entered and where a branch is taken,
//! the only ways to run longer than one word's straight-line code. Past the
//! limits each stack has a word's worth of room, then a guard region, so a
//! word that pushes or pops past its stack faults instead of corrupting
//! memory. That is the one difference from the Rust machine, which reports
//! underflow as a trap.

use crate::arm64::*;
use crate::codespace::{CodeSpace, Offset};
use fixpt_engine::cellular::{DS_LIMIT, MARK_MARK, PROMPT_MARK, RS_LIMIT, Trap};
use fixpt_heap::layout::kind;
use fixpt_heap::layout::cellular::{CLOSURE_FREE0, CLOSURE_WORD, KIND, PRIMITIVES, ROUTINE_DOCOL, ROUTINES, WORD_CELL0, WORD_ENTRY, WORD_NAME};
use fixpt_heap::layout::{H_FIELDS, T_DISTANCE};
use fixpt_heap::value::{TAG_BLOBLET, TAG_PAIR, TAG_TRAILER};
use fixpt_heap::{Heap, Value};
use std::mem::offset_of;

mod state {
    include!("state.rs");
}
mod regcode;
pub use regcode::{assemble_adapter, assemble_register_word};
pub(crate) use state::{ROUTINE_SLOTS, State};

// The registers the machine lives in: all callee-saved, so they survive a
// call into Rust except for the heap's base, which is reloaded.
const BASE: Reg = 19;
const IP: Reg = 20;
const CUR: Reg = 21;
const DSP: Reg = 22;
const RSP: Reg = 23;
const ST: Reg = 24;
const TABLE: Reg = 25;
/// The frame pointer: the address of the running closure's slot 0.
const FP: Reg = 26;
/// The closure running.
const CLO: Reg = 27;
const FUEL: Reg = 28;
/// The link register: where register code's `ret` goes (`regcode`).
const LR: Reg = 30;
// Scratch.
const W: Reg = 9;
const X10: Reg = 10;
const X11: Reg = 11;
const X13: Reg = 13;
const X14: Reg = 14;
const X15: Reg = 15;
const X16: Reg = 16;

fn off(f: usize) -> u32 {
    f as u32
}

/// Field `k` of the bloblet whose `suffix + 4` is in a register, as an
/// offset from that register.
fn field_off(k: usize) -> i64 {
    -(4 + 8 * k as i64)
}

// --------------------------------------------------------------- assembly

#[derive(Copy, Clone)]
struct Label(usize);

/// Instructions with labels, patched when everything is placed.
struct Asm {
    code: Vec<u32>,
    /// Where each label is, in instructions from this code's start: below
    /// zero for one in the machine this code is placed after.
    labels: Vec<Option<i64>>,
    fixups: Vec<(usize, usize)>,
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
    /// Register code with a frame: how far below `FP` its link is, which
    /// `x30` is loaded from again after anything that may change it.
    link: Option<usize>,
    /// Every conditional branch to a label as the opposite condition over
    /// a `b`: for a word too long for their 19 bits (±1 MB), which
    /// [`Asm::branches_fit`] finds after a first assembly.
    long_branches: bool,
}

impl Asm {
    fn new() -> Asm {
        let mut a = Asm {
            code: Vec::new(),
            labels: Vec::new(),
            fixups: Vec::new(),
            stubs: Vec::new(),
            trap_common: Label(0),
            exit_common: Label(0),
            cont: None,
            target: None,
            at: 0,
            link: None,
            long_branches: false,
        };
        a.trap_common = a.label();
        a.exit_common = a.label();
        a
    }
    fn here(&self) -> usize {
        self.code.len()
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
        assert!(self.labels[l.0].is_none());
        self.labels[l.0] = Some(self.here() as i64);
    }
    fn to(&mut self, l: Label, w: u32) {
        self.fixups.push((self.here(), l.0));
        self.e(w);
    }
    fn b(&mut self, l: Label) {
        self.to(l, b(0));
    }
    fn bl_to(&mut self, l: Label) {
        self.to(l, bl(0));
    }
    fn b_cond(&mut self, c: Cond, l: Label) {
        if self.long_branches {
            // The opposite condition (its low bit flipped) past the `b`.
            self.e(b_cond(c, 2) ^ 1);
            self.b(l);
        } else {
            self.to(l, b_cond(c, 0));
        }
    }
    fn cbnz(&mut self, t: Reg, l: Label) {
        if self.long_branches {
            self.e(cbz(t, 2));
            self.b(l);
        } else {
            self.to(l, cbnz(t, 0));
        }
    }
    fn cbz(&mut self, t: Reg, l: Label) {
        if self.long_branches {
            self.e(cbnz(t, 2));
            self.b(l);
        } else {
            self.to(l, cbz(t, 0));
        }
    }
    /// Whether every branch to a label reaches it: a conditional one has
    /// 19 bits, ±2^18 instructions, `b` and `bl` 26. A word whose do not
    /// is assembled again with `long_branches`.
    fn branches_fit(&self) -> bool {
        self.fixups.iter().all(|&(at, l)| {
            let d = self.labels[l].map_or(0, |to| to - at as i64);
            let bits = if self.code[at] & 0x7C00_0000 == 0x1400_0000 { 26 } else { 19 };
            (-(1i64 << (bits - 1))..(1i64 << (bits - 1))).contains(&d)
        })
    }
    /// Trap with `trap` if `c` holds.
    fn trap_if(&mut self, c: Cond, trap: Trap) {
        let (code, aux) = trap.code();
        let l = self.label();
        self.b_cond(c, l);
        self.stubs.push((l, code, aux));
    }
    fn flush_stubs(&mut self) {
        for (l, code, aux) in std::mem::take(&mut self.stubs) {
            self.bind(l);
            self.e(movz(X13, code as u32, 0));
            self.e(movz(X14, aux as u32, 0));
            let t = self.trap_common;
            self.b(t);
        }
    }
    fn finish(mut self) -> Vec<u32> {
        for (at, l) in std::mem::take(&mut self.fixups) {
            let to = self.labels[l].expect("label never bound");
            let d = to - at as i64;
            let w = self.code[at];
            self.code[at] = if w & 0xFC00_0000 == 0x1400_0000 {
                b(d)
            } else if w & 0xFC00_0000 == 0x9400_0000 {
                bl(d)
            } else if w & 0xFF00_0010 == 0x5400_0000 {
                b_cond(cond_of(w), d)
            } else if w & 0xFF00_0000 == 0xB500_0000 {
                cbnz(w & 31, d)
            } else if w & 0xFF00_0000 == 0xB400_0000 {
                cbz(w & 31, d)
            } else {
                unreachable!("not a branch: {w:#x}")
            };
        }
        self.code
    }

    // --------------------------------------------------- machine sequences

    /// Dispatch on the cell in `x9`: the tail of `NEXT`, and how a word
    /// given to `execute` or to the machine is run.
    fn run_word_in_w(&mut self) {
        self.e(add(X11, BASE, W));
        self.e(ldur(X10, X11, field_off(WORD_ENTRY)));
        self.e(ldr_reg(X10, TABLE, X10));
        self.e(br(X10));
    }

    /// On to the next cell of this word: `NEXT`, or, in a word compiled to
    /// machine code, a jump to that cell's code.
    fn cont(&mut self) {
        match self.cont {
            Some(l) => self.b(l),
            None => self.next(),
        }
    }

    /// On from where `CUR` and the ip now are, `d` (8k) in `dreg`: into the
    /// word's machine code there, if it has some, else `NEXT`. Where
    /// control lands in another word: a call, a return.
    fn enter_cur(&mut self, dreg: Reg) {
        let cellular = self.label();
        self.e(add(X11, BASE, CUR));
        self.e(ldur(X10, X11, field_off(WORD_ENTRY)));
        self.cbz(X10, cellular);
        self.e(ldr(X16, ST, off(offset_of!(State, resume))));
        self.e(ldr_reg(X16, X16, X10));
        self.cbz(X16, cellular);
        self.e(ldr_reg(X16, X16, dreg));
        self.cbz(X16, cellular);
        self.e(br(X16));
        self.bind(cellular);
        self.next();
    }

    fn next(&mut self) {
        self.e(ldr_post(W, IP, -8));
        self.e(tst_low(W, 3));
        self.e(b_cond(Cond::Ne, 3));
        self.e(ldr_reg(X10, TABLE, W));
        self.e(br(X10));
        self.run_word_in_w();
    }

    /// Store the machine's registers into the state, the ip as `8k`.
    fn save(&mut self) {
        self.e(str(CUR, ST, off(offset_of!(State, cur))));
        self.e(add(X13, BASE, CUR));
        self.e(sub_imm(X13, X13, 4));
        self.e(sub(X13, X13, IP));
        self.e(str(X13, ST, off(offset_of!(State, d))));
        self.e(str(DSP, ST, off(offset_of!(State, dsp))));
        self.e(str(RSP, ST, off(offset_of!(State, rsp))));
        self.e(str(FUEL, ST, off(offset_of!(State, fuel))));
        self.fp_encode(X13);
        self.e(str(X13, ST, off(offset_of!(State, fp))));
        self.e(str(CLO, ST, off(offset_of!(State, clo))));
    }

    /// `reg` = the frame pointer as a return entry keeps it:
    /// `ds_base - 8 - FP`, the bits of its fixnum index.
    fn fp_encode(&mut self, reg: Reg) {
        self.e(ldr(reg, ST, off(offset_of!(State, ds_base))));
        self.e(sub_imm(reg, reg, 8));
        self.e(sub(reg, reg, FP));
    }

    /// `FP` from an encoded frame pointer in `reg` (clobbers `X16`).
    fn fp_decode(&mut self, reg: Reg) {
        self.e(ldr(X16, ST, off(offset_of!(State, ds_base))));
        self.e(sub_imm(X16, X16, 8));
        self.e(sub(FP, X16, reg));
    }

    /// `reg` = a constant Value.
    fn value(&mut self, reg: Reg, v: Value) {
        self.es(&mov_imm64(reg, v.raw()));
    }

    /// A taken branch's new ip. In a compiled word it is made from the
    /// word, not from the ip, so that a loop's iterations do not wait on
    /// one chain of ip updates through them all.
    fn branch_ip(&mut self) {
        match self.target {
            Some((_, to)) => {
                self.es(&mov_imm64(X13, (4 + 8 * (WORD_CELL0 + to)) as u64));
                self.e(add(IP, BASE, CUR));
                self.e(sub(IP, IP, X13));
            }
            None => self.e(sub(IP, IP, X13)),
        }
    }

    /// Push a return entry, `(CUR, 8k, fp, CLO)`, from this word as it
    /// stands: the ip already past what this routine consumed.
    fn push_return(&mut self) {
        self.e(add(X13, BASE, CUR));
        self.e(sub_imm(X13, X13, 4));
        self.e(sub(X13, X13, IP));
        self.fp_encode(X14);
        self.e(stp_pre(X14, CLO, RSP, -16));
        self.e(stp_pre(CUR, X13, RSP, -16));
    }

    /// The same, marked as register code's `blr` pushes it (`regcode`):
    /// its `8k` negated.
    fn push_return_marked(&mut self) {
        self.e(add(X13, BASE, CUR));
        self.e(sub_imm(X13, X13, 4));
        self.e(sub(X13, IP, X13));
        self.fp_encode(X14);
        self.e(stp_pre(X14, CLO, RSP, -16));
        self.e(stp_pre(CUR, X13, RSP, -16));
    }

    /// The return entry on top made plain, if register code's `blr`
    /// marked it: before a tail call of stack code, which returns the
    /// stack's way.
    fn unmark_return(&mut self) {
        let plain = self.label();
        self.e(ldr(X13, RSP, 8));
        self.e(cmp_imm(X13, 0));
        self.b_cond(Cond::Ge, plain);
        self.e(sub(X13, XZR, X13));
        self.e(str(X13, RSP, 8));
        self.bind(plain);
    }

    /// Pop a return entry and return to it, or leave the machine at the
    /// bottom one (whose word is `#f`). Prompts' and marks' entries are
    /// not returns: pass them by.
    fn pop_return(&mut self) {
        self.pop_return_of(false);
    }

    /// The same; with `marked`, an entry register code's `blr` pushed (its
    /// `8k` negated, `regcode`) is returned to the stack's way all the
    /// same. Only register code's own `return` can meet one: stack code is
    /// never called with one.
    fn pop_return_of(&mut self, marked: bool) {
        let again = self.label();
        self.bind(again);
        self.e(ldr(X13, RSP, 0));
        for mark in [PROMPT_MARK, MARK_MARK] {
            let not = self.label();
            self.value(X15, mark);
            self.e(cmp(X13, X15));
            self.b_cond(Cond::Ne, not);
            self.e(add_imm(RSP, RSP, 32));
            self.b(again);
            self.bind(not);
        }
        self.e(ldp_post(CUR, X13, RSP, 16));
        if marked {
            let plain = self.label();
            self.e(cmp_imm(X13, 0));
            self.b_cond(Cond::Ge, plain);
            self.e(sub(X13, XZR, X13));
            self.bind(plain);
        }
        self.e(ldp_post(X14, CLO, RSP, 16));
        self.value(X15, Value::FALSE);
        self.e(cmp(CUR, X15));
        let ec = self.exit_common;
        self.b_cond(Cond::Eq, ec);
        self.e(add(IP, BASE, CUR));
        self.e(sub_imm(IP, IP, 4));
        self.e(sub(IP, IP, X13));
        self.fp_decode(X14);
        self.enter_cur(X13);
    }

    /// Check that `reg` is a cellular closure, else go to `not`: its
    /// trailer says F, and its header, F + 1 words back, its kind.
    fn is_closure(&mut self, reg: Reg, not: Label) {
        self.e(and_low(X13, reg, 3));
        self.e(cmp_imm(X13, TAG_BLOBLET as u32));
        self.b_cond(Cond::Ne, not);
        self.e(add(X11, BASE, reg));
        self.e(ldur(X15, X11, field_off(1)));
        self.e(and_low(X13, X15, 3));
        self.e(cmp_imm(X13, TAG_TRAILER as u32));
        self.b_cond(Cond::Ne, not);
        self.e(sub(X14, X11, X15));
        self.e(ldur(X14, X14, -7));
        self.e(ubfx(X14, X14, 3, 8));
        self.e(cmp_imm(X14, kind("cellular-closure") as u32));
        self.b_cond(Cond::Ne, not);
    }

    /// Load them back, recomputing the ip from `cur`, `d` and the base.
    fn load(&mut self) {
        self.e(ldr(BASE, ST, off(offset_of!(State, base))));
        self.e(ldr(CUR, ST, off(offset_of!(State, cur))));
        self.e(ldr(X13, ST, off(offset_of!(State, d))));
        self.e(add(IP, BASE, CUR));
        self.e(sub_imm(IP, IP, 4));
        self.e(sub(IP, IP, X13));
        self.e(ldr(DSP, ST, off(offset_of!(State, dsp))));
        self.e(ldr(RSP, ST, off(offset_of!(State, rsp))));
        self.e(ldr(TABLE, ST, off(offset_of!(State, table))));
        self.e(ldr(FUEL, ST, off(offset_of!(State, fuel))));
        self.e(ldr(CLO, ST, off(offset_of!(State, clo))));
        self.e(ldr(X14, ST, off(offset_of!(State, fp))));
        self.fp_decode(X14);
    }

    fn fuel(&mut self) {
        self.e(subs_imm(FUEL, FUEL, 1));
        self.trap_if(Cond::Eq, Trap::OutOfFuel);
    }

    /// A taken branch's poll: only a backward one can make a loop, so a
    /// branch known to go forward (in a compiled word) makes none.
    fn fuel_unless_forward(&mut self) {
        if !matches!(self.target, Some((_, to)) if to > self.at) {
            self.fuel();
        }
    }

    fn ds_limit(&mut self) {
        self.e(ldr(X13, ST, off(offset_of!(State, ds_limit))));
        self.e(cmp(DSP, X13));
        self.trap_if(Cond::Lo, Trap::StackOverflow);
    }

    fn rs_limit(&mut self) {
        self.e(ldr(X13, ST, off(offset_of!(State, rs_limit))));
        self.e(cmp(RSP, X13));
        self.trap_if(Cond::Ls, Trap::TooDeep);
    }

    /// Leave machine code for the Rust side of routine `n`; carry on
    /// unless it reports a trap: with this word's next cell if the routine
    /// only computes, or from wherever it left the machine (control).
    fn callout(&mut self, n: u64) {
        self.save();
        self.e(mov(0, ST));
        self.e(movz(1, n as u32, 0));
        self.e(ldr(X16, ST, off(offset_of!(State, callout))));
        self.e(blr(X16));
        let exit = self.exit_common;
        self.cbnz(0, exit);
        self.load();
        if CONTROL_CALLOUTS.contains(&ROUTINES[n as usize].0) {
            self.enter_cur(X13);
        } else {
            self.cont();
        }
    }

    /// `x13` = top, `x14` = the one below; trap unless both are fixnums.
    fn two_fixnums(&mut self, name: &'static str) {
        self.e(ldp(X13, X14, DSP, 0));
        self.e(orr(X15, X13, X14));
        self.e(tst_low(X15, 3));
        self.trap_if(Cond::Ne, Trap::Type { routine: name });
    }

    /// `x13` = the tag of `reg`, compared with `tag`.
    fn check_tag(&mut self, reg: Reg, tag: u64, trap: Trap) {
        self.e(and_low(X13, reg, 3));
        self.e(cmp_imm(X13, tag as u32));
        self.trap_if(Cond::Ne, trap);
    }
}

fn cond_of(w: u32) -> Cond {
    use Cond::*;
    [Eq, Ne, Hs, Lo, Vs, Vc, Hi, Ls, Ge, Lt, Gt, Le]
        .into_iter()
        .find(|c| *c as u32 == w & 15)
        .expect("a condition we emit")
}

/// The whole machine: an entry routine, the common exits, and one routine per
/// routine number. Returns the code and where each routine starts.
fn generate() -> (Vec<u32>, usize, Vec<usize>, [i64; 2]) {
    let mut a = Asm::new();

    // The entry, called from Rust with the state in x0.
    let entry = a.here();
    a.es(&[
        stp_pre(29, 30, SP, -96),
        add_imm(29, SP, 0),
        stp(19, 20, SP, 16),
        stp(21, 22, SP, 32),
        stp(23, 24, SP, 48),
        stp(25, 26, SP, 64),
        stp(27, 28, SP, 80),
        mov(ST, 0),
    ]);
    a.load();
    a.e(ldr(W, ST, off(offset_of!(State, start))));
    a.run_word_in_w();

    // A trap: code in x13 and detail in x14; then the common exit.
    let (tc, ec) = (a.trap_common, a.exit_common);
    a.bind(tc);
    a.e(str(X13, ST, off(offset_of!(State, status))));
    a.e(str(X14, ST, off(offset_of!(State, aux))));
    a.bind(ec);
    a.save();
    a.es(&[
        ldp(27, 28, SP, 80),
        ldp(25, 26, SP, 64),
        ldp(23, 24, SP, 48),
        ldp(21, 22, SP, 32),
        ldp(19, 20, SP, 16),
        ldp_post(29, 30, SP, 96),
        ret(),
    ]);

    let mut starts = Vec::new();
    for (n, (name, _)) in ROUTINES.iter().enumerate() {
        while !a.here().is_multiple_of(4) {
            a.e(0xD503_201F); // nop: routines start 16-aligned
        }
        starts.push(a.here());
        routine_body(&mut a, n, name);
        a.flush_stubs();
    }
    let commons = [a.trap_common, a.exit_common].map(|l| a.labels[l.0].expect("bound"));
    (a.finish(), entry, starts, commons)
}

/// Routine `n`'s code: in the machine, ending in `NEXT`; or, in a word
/// compiled to machine code (`a.cont` set), going on to the next cell's.
fn routine_body(a: &mut Asm, n: usize, name: &'static str) {
    match name {
        "docol" => {
            // x9 is the word and x11 its suffix + 4.
            a.fuel();
            a.ds_limit();
            a.rs_limit();
            a.push_return();
            a.e(mov(CUR, W));
            a.e(sub_imm(IP, X11, (4 + 8 * WORD_CELL0) as u32));
            a.next();
        }
        "exit" => a.pop_return(),
        "halt" => {
            let ec = a.exit_common;
            a.b(ec);
        }
        "lit" => {
            a.e(ldr_post(X13, IP, -8));
            a.e(str_pre(X13, DSP, -8));
            a.cont();
        }
        "branch" => {
            if a.target.is_none() {
                a.e(ldr_post(X13, IP, -8));
            }
            a.branch_ip();
            a.fuel_unless_forward();
            a.ds_limit();
            match a.target {
                Some((t, _)) => a.b(t),
                None => a.next(),
            }
        }
        "0branch" => {
            let skip = a.label();
            a.e(ldr_post(X14, DSP, 8));
            a.e(ldr_post(X13, IP, -8));
            a.value(X15, Value::FALSE);
            a.e(cmp(X14, X15));
            a.b_cond(Cond::Ne, skip);
            a.branch_ip();
            a.fuel_unless_forward();
            a.ds_limit();
            match a.target {
                Some((t, _)) => {
                    a.b(t);
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
            a.e(ldr_post(W, DSP, 8));
            a.e(tst_low(W, 3));
            a.b_cond(Cond::Ne, is_ref);
            // A primitive, by number: 1 ≤ n < PRIMITIVES.
            a.cbz(W, bad);
            a.e(cmp_imm(W, (8 * PRIMITIVES) as u32));
            a.b_cond(Cond::Hs, bad);
            a.e(ldr_reg(X10, TABLE, W));
            a.e(br(X10));
            a.bind(bad);
            a.e(movz(X13, Trap::NoRoutine(0).code().0 as u32, 0));
            a.e(asr_imm(X14, W, 3));
            let tc = a.trap_common;
            a.b(tc);
            // A word: a bloblet with a trailer, whose header says kind 33.
            a.bind(is_ref);
            a.check_tag(W, TAG_BLOBLET, Trap::NotAWord);
            a.e(add(X11, BASE, W));
            a.e(ldur(X15, X11, field_off(1)));
            a.check_tag(X15, TAG_TRAILER, Trap::NotAWord);
            // The header is F + 1 words before the suffix, and the
            // trailer is F << 3 | 5: header = x11 - 4 - 8 - 8F.
            a.e(sub(X14, X11, X15));
            a.e(ldur(X14, X14, -7));
            a.e(ubfx(X14, X14, 3, 8));
            a.e(cmp_imm(X14, KIND as u32));
            a.trap_if(Cond::Ne, Trap::NotAWord);
            a.run_word_in_w();
        }
        "dup" => {
            a.e(ldr(X13, DSP, 0));
            a.e(str_pre(X13, DSP, -8));
            a.cont();
        }
        "drop" => {
            a.e(add_imm(DSP, DSP, 8));
            a.cont();
        }
        "swap" => {
            a.e(ldp(X13, X14, DSP, 0));
            a.e(stp(X14, X13, DSP, 0));
            a.cont();
        }
        "over" => {
            a.e(ldr(X13, DSP, 8));
            a.e(str_pre(X13, DSP, -8));
            a.cont();
        }
        "+" | "-" => {
            a.two_fixnums(name);
            a.e(if name == "+" { adds(X15, X14, X13) } else { subs(X15, X14, X13) });
            a.trap_if(Cond::Vs, Trap::Overflow { routine: name });
            a.e(str_pre(X15, DSP, 8));
            a.cont();
        }
        "<" => {
            a.two_fixnums(name);
            a.e(cmp(X14, X13));
            a.value(X16, Value::TRUE);
            a.value(X15, Value::FALSE);
            a.e(csel(X15, X16, X15, Cond::Lt));
            a.e(str_pre(X15, DSP, 8));
            a.cont();
        }
        "eq" => {
            a.e(ldp(X13, X14, DSP, 0));
            a.e(cmp(X14, X13));
            a.value(X16, Value::TRUE);
            a.value(X15, Value::FALSE);
            a.e(csel(X15, X16, X15, Cond::Eq));
            a.e(str_pre(X15, DSP, 8));
            a.cont();
        }
        "car" | "cdr" => {
            a.e(ldr(X15, DSP, 0));
            a.check_tag(X15, TAG_PAIR, Trap::Type { routine: name });
            a.e(add(X14, BASE, X15));
            a.e(ldur(X15, X14, if name == "car" { -1 } else { 7 }));
            a.e(str(X15, DSP, 0));
            a.cont();
        }
        // Typed: the checker has proved the operands ints. Fixnums here; a
        // bignum, or a sum past a fixnum, the Rust machine's (PLAN.md, Q2).
        "int-add" | "int-sub" => {
            let slow = a.label();
            a.e(ldp(X13, X14, DSP, 0));
            a.e(orr(X15, X13, X14));
            a.e(tst_low(X15, 3));
            a.b_cond(Cond::Ne, slow);
            a.e(if name == "int-add" { adds(X15, X14, X13) } else { subs(X15, X14, X13) });
            a.b_cond(Cond::Vs, slow);
            a.e(str_pre(X15, DSP, 8));
            a.cont();
            a.bind(slow);
            a.callout(n as u64);
        }
        "int-less" | "int-eq" => {
            let slow = a.label();
            a.e(ldp(X13, X14, DSP, 0));
            a.e(orr(X15, X13, X14));
            a.e(tst_low(X15, 3));
            a.b_cond(Cond::Ne, slow);
            a.e(cmp(X14, X13));
            a.value(X16, Value::TRUE);
            a.value(X15, Value::FALSE);
            a.e(csel(X15, X16, X15, if name == "int-less" { Cond::Lt } else { Cond::Eq }));
            a.e(str_pre(X15, DSP, 8));
            a.cont();
            a.bind(slow);
            a.callout(n as u64);
        }
        // A list may be `nil`: `car` of it traps, as the Rust machine's does.
        "pair-car" | "pair-cdr" => {
            a.e(ldr(X15, DSP, 0));
            a.check_tag(X15, TAG_PAIR, Trap::Type { routine: name });
            a.e(add(X14, BASE, X15));
            a.e(ldur(X15, X14, if name == "pair-car" { -1 } else { 7 }));
            a.e(str(X15, DSP, 0));
            a.cont();
        }
        "field" => {
            // Field k is 8k bytes before the bloblet's suffix; x13 is 8k.
            a.e(ldr_post(X13, IP, -8));
            a.e(ldr(X14, DSP, 0));
            a.e(add(X11, BASE, X14));
            a.e(sub(X16, X11, X13));
            a.e(ldur(X15, X16, -4));
            a.e(str(X15, DSP, 0));
            a.cont();
        }
        "field@" => {
            // The fast path: a bloblet with a trailer, which says F.
            let slow = a.label();
            a.e(ldp(X15, X14, DSP, 0));
            a.e(tst_low(X15, 3));
            a.trap_if(Cond::Ne, Trap::Type { routine: name });
            a.check_tag(X14, TAG_BLOBLET, Trap::Type { routine: name });
            a.e(add(X11, BASE, X14));
            a.e(ldur(X16, X11, field_off(1)));
            a.e(and_low(X13, X16, 3));
            a.e(cmp_imm(X13, TAG_TRAILER as u32));
            a.b_cond(Cond::Ne, slow);
            // 2 ≤ k ≤ F; 8k is x15 and 8F is the trailer less its tag.
            a.e(cmp_imm(X15, 16));
            a.trap_if(Cond::Lt, Trap::Field { routine: name });
            a.e(sub_imm(X16, X16, TAG_TRAILER as u32));
            a.e(cmp(X15, X16));
            a.trap_if(Cond::Gt, Trap::Field { routine: name });
            a.e(sub(X16, X11, X15));
            a.e(ldur(X15, X16, -4));
            a.e(str_pre(X15, DSP, 8));
            a.cont();
            a.bind(slow);
            a.callout(n as u64);
        }
        // Code compiled from FX-26: frames on the data stack, flat
        // closures, globals, calls; as `fixpt_engine::cellular` has them.
        "slot" | "slot!" => {
            // Slot i is 8i bytes below FP, and must be on the stack.
            a.e(ldr_post(X13, IP, -8));
            a.e(sub(X14, FP, X13));
            if name == "slot!" {
                a.e(ldr_post(X15, DSP, 8));
            }
            a.e(cmp(X14, DSP));
            a.trap_if(Cond::Lo, Trap::Field { routine: name });
            if name == "slot" {
                a.e(ldr(X15, X14, 0));
                a.e(str_pre(X15, DSP, -8));
            } else {
                a.e(str(X15, X14, 0));
            }
            a.cont();
        }
        "free" => {
            // Field CLOSURE_FREE0 + i of the closure running, if it has it.
            let bad = a.label();
            a.e(ldr_post(X10, IP, -8));
            a.is_closure(CLO, bad);
            a.e(add_imm(X10, X10, (8 * CLOSURE_FREE0) as u32));
            a.e(sub_imm(X16, X15, TAG_TRAILER as u32));
            a.e(cmp(X10, X16));
            a.b_cond(Cond::Gt, bad);
            a.e(sub(X14, X11, X10));
            a.e(ldur(X15, X14, -4));
            a.e(str_pre(X15, DSP, -8));
            a.cont();
            a.bind(bad);
            let (code, aux) = Trap::Field { routine: name }.code();
            a.e(movz(X13, code as u32, 0));
            a.e(movz(X14, aux as u32, 0));
            let tc = a.trap_common;
            a.b(tc);
        }
        "global" | "global!" => {
            // The cell's value is its field 2 (checked when the word was
            // made).
            a.e(ldr_post(X13, IP, -8));
            a.e(add(X11, BASE, X13));
            if name == "global" {
                a.e(ldur(X15, X11, field_off(2)));
                a.e(str_pre(X15, DSP, -8));
            } else {
                a.e(ldr_post(X15, DSP, 8));
                a.e(stur(X15, X11, field_off(2)));
                // One more write, for the guards (`global-guard`).
                a.e(ldur(X16, X11, field_off(fixpt_heap::layout::cellular::GLOBAL_WRITES)));
                a.e(add_imm(X16, X16, Value::fixnum(1).raw() as u32));
                a.e(stur(X16, X11, field_off(fixpt_heap::layout::cellular::GLOBAL_WRITES)));
                a.es(&card_mark(X11, field_off(2), ST, off(offset_of!(State, cards)), X13, X16));
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
            a.e(ldr(W, DSP, 0));
            if !typed {
                a.is_closure(W, other);
            }
            a.fuel();
            if !(typed && name == "tailcall") {
                a.ds_limit();
                a.rs_limit();
            }
            // The count, 8n, in X10: `push_return` uses X13 and X14.
            a.e(ldr_post(X10, IP, -8));
            a.e(add_imm(DSP, DSP, 8));
            if name == "call" {
                a.push_return();
                // Slot 0 is the first argument, the deepest: DSP + 8n - 8.
                a.e(add(X14, DSP, X10));
                a.e(sub_imm(FP, X14, 8));
            } else {
                // Slide the n arguments down over this frame, deepest
                // first; FP stays.
                let (top, done) = (a.label(), a.label());
                a.e(add(X14, DSP, X10));
                a.e(sub_imm(X14, X14, 8));
                a.e(mov(X15, FP));
                a.e(mov(X16, X10));
                a.bind(top);
                a.cbz(X16, done);
                a.e(ldr_post(X10, X14, -8));
                a.e(str_post(X10, X15, -8));
                a.e(sub_imm(X16, X16, 8));
                a.b(top);
                a.bind(done);
                a.e(add_imm(DSP, X15, 8));
            }
            a.e(mov(CLO, W));
            a.e(add(X11, BASE, W));
            a.e(ldur(CUR, X11, field_off(CLOSURE_WORD)));
            a.e(add(IP, BASE, CUR));
            a.e(sub_imm(IP, IP, (4 + 8 * WORD_CELL0) as u32));
            a.e(movz(X13, (8 * WORD_CELL0) as u32, 0));
            a.enter_cur(X13);
            a.bind(other);
            if !typed {
                a.callout(n as u64);
            }
        }
        "return" => {
            // The value on top replaces the frame; then back.
            a.e(ldr_post(X15, DSP, 8));
            a.e(add_imm(X14, FP, 8));
            a.e(cmp(DSP, X14));
            a.trap_if(Cond::Hi, Trap::Underflow { routine: name });
            a.e(mov(DSP, FP));
            a.e(str(X15, DSP, 0));
            a.pop_return();
        }
        // Everything else: the Rust machine runs it on these stacks
        // (`callout`), so it means exactly what it means there.
        _ => a.callout(n as u64),
    }
}

/// A word's cells as machine code, for a place from which the machine's
/// common trap and exit are `far` instructions away (step 11a): the code,
/// and where each cell's code starts, in instructions, or -1 for a cell
/// that is an operand. [`NativeMachine::compile_word`] places it; the
/// compiler written in FX-26 must make exactly this.
pub fn assemble_word(heap: &Heap, word: Value, far: [i64; 2]) -> Result<(Vec<u32>, Vec<i64>), String> {
    assemble_word_as(heap, word, far, false)
}

/// [`assemble_word`], with every conditional branch long if `long`.
fn assemble_word_as(heap: &Heap, word: Value, far: [i64; 2], long: bool) -> Result<(Vec<u32>, Vec<i64>), String> {
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
    a.long_branches = long;
    let labels: Vec<Label> = (0..=cells.len()).map(|_| a.label()).collect();
    // The machine's common exit is a conditional branch away from some
    // routines, too far from a large word's code: each cell's goes to a
    // jump of its own, placed after it.
    let far_exit = a.exit_common;
    // As a cell: `docol`'s work, then the first cell.
    a.fuel();
    a.ds_limit();
    a.rs_limit();
    a.push_return();
    a.e(mov(CUR, W));
    a.e(sub_imm(IP, X11, (4 + 8 * WORD_CELL0) as u32));
    a.b(labels[0]);
    a.flush_stubs();
    for (i, cell) in cells.iter().enumerate() {
        if !starts[i] {
            continue;
        }
        a.bind(labels[i]);
        let near_exit = a.label();
        a.exit_common = near_exit;
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
            a.e(sub_imm(IP, IP, 8));
            routine_body(&mut a, n, name);
        } else {
            a.cont = None;
            a.target = None;
            a.e(ldr_post(W, IP, -8));
            a.run_word_in_w();
        }
        a.flush_stubs();
        a.bind(near_exit);
        a.b(far_exit);
    }
    a.exit_common = far_exit;
    // The machine's common trap and exit, through the state: no branch
    // leaves this code, so it may be placed anywhere, and run by any
    // machine.
    let _ = far;
    let [tc, ec] = [a.trap_common, a.exit_common];
    a.bind(tc);
    a.e(ldr(X16, ST, off(offset_of!(State, trap))));
    a.e(br(X16));
    a.bind(ec);
    a.e(ldr(X16, ST, off(offset_of!(State, exit))));
    a.e(br(X16));
    // Too long for a conditional branch to reach (B1): again, long.
    if !long && !a.branches_fit() {
        return assemble_word_as(heap, word, far, true);
    }
    let at: Vec<i64> = (0..cells.len()).map(|i| if starts[i] { a.labels[labels[i].0].expect("bound") } else { -1 }).collect();
    Ok((a.finish(), at))
}

/// Routines whose call-out leaves the machine somewhere other than the next
/// cell: after them, the machine goes on from wherever it is (`enter_cur`).
pub const CONTROL_CALLOUTS: &[&str] = &[
    "prompt", "abort", "callcomp", "callcc", "withmark", "withmark-tail", "call", "tailcall", "execute", "docol", "exit", "halt",
    "return", "tcall", "ttailcall", "resume", "undefined",
];

/// What the compiler written in FX-26 needs to know of this machine to
/// make the code [`NativeMachine::compile_word`] does, as FX-26
/// definitions: `src/native-layout.fx` in `fixpt-fx26`, which a test keeps
/// equal to this.
pub fn fx26_module() -> String {
    let mut out = String::from(
        ";;; Generated by `fixpt_native::cellular::fx26_module` from the hand-encoded\n\
         ;;; machine; `FIXPT_BLESS=1 cargo test -p fixpt-fx26 --test layout` rewrites it.\n\n",
    );
    let mut c = |name: &str, v: i64, what: &str| out.push_str(&format!("(define {name} int {v})  ; {what}\n"));
    for (name, r) in [
        ("n-base", BASE), ("n-ip", IP), ("n-cur", CUR), ("n-dsp", DSP), ("n-rsp", RSP), ("n-st", ST), ("n-table", TABLE),
        ("n-fp", FP), ("n-clo", CLO), ("n-fuel", FUEL), ("n-w", W), ("n-x10", X10), ("n-x11", X11), ("n-x13", X13),
        ("n-x14", X14), ("n-x15", X15), ("n-x16", X16),
    ] {
        c(name, r as i64, "a register");
    }
    for (name, o) in [
        ("n-st-base", offset_of!(State, base)), ("n-st-cur", offset_of!(State, cur)), ("n-st-d", offset_of!(State, d)),
        ("n-st-dsp", offset_of!(State, dsp)), ("n-st-rsp", offset_of!(State, rsp)), ("n-st-table", offset_of!(State, table)),
        ("n-st-fuel", offset_of!(State, fuel)), ("n-st-callout", offset_of!(State, callout)),
        ("n-st-ds-base", offset_of!(State, ds_base)), ("n-st-ds-limit", offset_of!(State, ds_limit)),
        ("n-st-rs-limit", offset_of!(State, rs_limit)), ("n-st-fp", offset_of!(State, fp)), ("n-st-clo", offset_of!(State, clo)),
        ("n-st-resume", offset_of!(State, resume)), ("n-st-trap", offset_of!(State, trap)),
        ("n-st-exit", offset_of!(State, exit)), ("n-st-cards", offset_of!(State, cards)),
    ] {
        c(name, o as i64, "a State field's offset");
    }
    for (name, v) in [("n-false", Value::FALSE), ("n-true", Value::TRUE), ("n-prompt-mark", PROMPT_MARK), ("n-mark-mark", MARK_MARK)] {
        c(name, v.raw() as i64, "a Value's bits");
    }
    for (name, v, what) in [
        ("n-tag-bloblet", TAG_BLOBLET, "a tag"),
        ("n-tag-pair", TAG_PAIR, "a tag"),
        ("n-tag-trailer", TAG_TRAILER, "a tag"),
        ("n-kind-word", KIND as u64, "the kind of a cellular word"),
        ("n-kind-closure", kind("cellular-closure") as u64, "the kind of a cellular closure"),
        ("n-closure-word", CLOSURE_WORD as u64, "a closure's field"),
        ("n-closure-free0", CLOSURE_FREE0 as u64, "a closure's field"),
        ("n-word-entry", WORD_ENTRY as u64, "a word's field"),
        ("n-word-cell0", WORD_CELL0 as u64, "a word's field"),
        ("n-primitives", PRIMITIVES as u64, "routines that may be cells"),
    ] {
        c(name, v as i64, what);
    }
    for (name, t) in [
        ("n-trap-type", Trap::Type { routine: "+" }), ("n-trap-overflow", Trap::Overflow { routine: "+" }),
        ("n-trap-underflow", Trap::Underflow { routine: "+" }), ("n-trap-field", Trap::Field { routine: "+" }),
        ("n-trap-no-routine", Trap::NoRoutine(0)), ("n-trap-not-a-word", Trap::NotAWord), ("n-trap-out-of-fuel", Trap::OutOfFuel),
        ("n-trap-stack-overflow", Trap::StackOverflow), ("n-trap-too-deep", Trap::TooDeep),
    ] {
        c(name, t.code().0 as i64, "a trap's code; a routine's number is its detail");
    }
    out.push_str("\n;; How many operand cells follow routine `n`.\n");
    out.push_str("(define n-operands (subr pure (int) int)\n  (lambda (n)\n    (case n\n");
    for (i, (name, _)) in ROUTINES.iter().enumerate() {
        let k = fixpt_heap::layout::cellular::operands(name);
        if k > 0 {
            out.push_str(&format!("      (({i}) {k})  ; {name}\n"));
        }
    }
    out.push_str("      (else 0))))\n\n");
    out.push_str(";; Whether routine `n`'s call-out may leave the machine anywhere.\n");
    out.push_str("(define n-control? (subr pure (int) bool)\n  (lambda (n)\n    (case n\n");
    for (i, (name, _)) in ROUTINES.iter().enumerate() {
        if CONTROL_CALLOUTS.contains(name) {
            out.push_str(&format!("      (({i}) #t)  ; {name}\n"));
        }
    }
    out.push_str("      (else #f))))\n");
    fixpt_heap::layout::fx26_as_module("native-layout-module", &out)
}

// Invariants the generated code bakes in.
const _: () = assert!(PRIMITIVES <= ROUTINE_SLOTS, "State::routines has a slot for every routine");
const _: () = assert!(T_DISTANCE.lo == 3 && H_FIELDS.lo > 10, "the trailer holds F << 3, the kind is bits 3..11");
const _: () = assert!(ROUTINE_DOCOL == 0, "a zero cell is not a primitive");

// ------------------------------------------------------------------ Rust side

/// What the machine calls for routines it leaves to Rust. Returns nonzero
/// if it set a trap in the state.
extern "C" fn callout(st: *mut State, n: u64) -> u64 {
    // SAFETY: `st` is the state `NativeMachine::run` passed in, alive for
    // the whole run; its `heap` is the heap `run` holds exclusively; and the
    // stacks are the machine's, between their pointers and bases. The
    // machine is stopped at a safepoint with every register saved.
    let st = unsafe { &mut *st };
    let heap = unsafe { heap_of(st) };
    let nds = (st.ds_base - st.dsp) as usize / 8;
    let nrs = (st.rs_base - st.rsp) as usize / 8;
    let ds = unsafe { std::slice::from_raw_parts_mut(st.dsp as *mut Value, nds) };
    let rs = unsafe { std::slice::from_raw_parts_mut(st.rsp as *mut Value, nrs) };
    let name = ROUTINES[n as usize].0;
    CALLOUTS.with(|c| c.borrow_mut()[n as usize] += 1);
    let started = TIMING.with(|t| *t).then(std::time::Instant::now);
    let out = callout_on(st, n, name, heap, ds, rs);
    if let Some(t) = started {
        CALLOUT_NANOS.with(|c| c.borrow_mut()[n as usize] += t.elapsed().as_nanos() as u64);
    }
    out
}

/// What `pure_call` gives: the value, and whether the primitive failed.
#[repr(C)]
pub(crate) struct PureOut {
    v: u64,
    failed: u64,
}

/// Register code's call of primitive `p`, one that never collects
/// (`fixpt_runtime::never_collects`), on `x`, and `y` if it takes two: no
/// safepoint, so the machine's registers need not be where a collection
/// would find them. A failure's message is kept for the trap to report.
pub(crate) extern "C" fn pure_call(st: *mut State, p: u64, x: u64, y: u64) -> PureOut {
    // SAFETY: `st` is the state the machine runs with; its `rt`, when not
    // 0, the runtime `run_in_runtime` holds exclusively.
    let st = unsafe { &mut *st };
    let fail = |m: String| {
        LAST_MESSAGE.with(|c| *c.borrow_mut() = Some(m));
        PureOut { v: 0, failed: 1 }
    };
    if st.rt == 0 {
        return fail("no runtime to call a primitive in".into());
    }
    let rt = unsafe { &mut *(st.rt as *mut fixpt_runtime::Runtime) };
    let def = &fixpt_runtime::PRIMITIVES[p as usize];
    let fixpt_runtime::PrimKind::Simple(f) = def.kind else { return fail(format!("`{}` needs an engine", def.name)) };
    // On the stack: a call per primitive run, no allocation for it.
    let mut buf = [Value(x), Value(y)];
    let args = if def.min == 1 { &mut buf[..1] } else { &mut buf[..] };
    let out = match f(rt, args) {
        Ok(v) => PureOut { v: v.raw(), failed: 0 },
        Err(t) => fail(fixpt_engine::cellular::describe(rt, t.obj)),
    };
    st.alloc_limit = rt.heap.inline_limit() as u64;
    out
}

fn callout_on(st: &mut State, n: u64, name: &'static str, heap: &mut Heap, ds: &mut [Value], rs: &mut [Value]) -> u64 {
    if !matches!(name, "field@" | "field!" | "cons") {
        let result = match name {
            "prim" => prim(st),
            "closure" => closure(st),
            _ => {
                // SAFETY: as for `heap` above; this is the only use of it now.
                let heap = unsafe { heap_of(st) };
                match crate::control::run(st, heap, name, safepoint) {
                    Some(r) => r,
                    None => round_trip(st, n),
                }
            }
        };
        // SAFETY: as above.
        let heap = unsafe { heap_of(st) };
        st.base = 0;
        st.alloc_limit = heap.inline_limit() as u64;
        return match result {
            Ok(()) => 0,
            Err(t) => {
                let (code, aux) = t.code();
                if let Trap::Prim(m) = &t {
                    LAST_MESSAGE.with(|c| *c.borrow_mut() = Some(m.clone()));
                }
                st.status = code;
                st.aux = aux;
                1
            }
        };
    }
    let result = callout_routine(heap, st, ds, rs, name);
    st.base = 0;
    st.alloc_limit = heap.inline_limit() as u64;
    match result {
        Ok(pop) => {
            st.dsp += 8 * pop as u64;
            0
        }
        Err(t) => {
            let (code, aux) = t.code();
            st.status = code;
            st.aux = aux;
            1
        }
    }
}

/// How many times this thread's machines have called out to Rust for
/// each routine, by name, since the last call: where the machine code
/// leaves the most to Rust.
pub fn take_callout_counts() -> Vec<(&'static str, u64)> {
    let counts = CALLOUTS.with(|c| std::mem::replace(&mut *c.borrow_mut(), [0; ROUTINES.len()]));
    ROUTINES.iter().zip(counts).filter(|(_, n)| *n > 0).map(|((name, _), n)| (*name, n)).collect()
}

/// And the time spent in each, in nanoseconds, when `FIXPT_CALLOUTS` is set.
pub fn take_callout_nanos() -> Vec<(&'static str, u64)> {
    let nanos = CALLOUT_NANOS.with(|c| std::mem::replace(&mut *c.borrow_mut(), [0; ROUTINES.len()]));
    ROUTINES.iter().zip(nanos).filter(|(_, n)| *n > 0).map(|((name, _), n)| (*name, n)).collect()
}

/// With `FIXPT_CALLOUTS` set, write the callout counts to stderr: after
/// each `run_word`, so from the command line too.
pub fn report_callouts() {
    if TIMING.with(|t| *t) {
        eprintln!("callouts: {:?}", take_callout_counts());
        let ms: Vec<(&str, u64)> = take_callout_nanos().into_iter().map(|(n, t)| (n, t / 1_000_000)).collect();
        eprintln!("callout ms: {ms:?}");
        eprintln!("round trips lifted {} words of stack", ROUND_TRIP_WORDS.with(|w| std::mem::take(&mut *w.borrow_mut())));
        let (words, n) = CAPTURED.with(|c| std::mem::take(&mut *c.borrow_mut()));
        eprintln!("continuations captured: {n}, {words} words of stack in all");
        let mut prims: Vec<(&str, u64)> = PRIM_COUNTS.with(|c| std::mem::take(&mut *c.borrow_mut())).into_iter().collect();
        prims.sort_by_key(|(_, n)| std::cmp::Reverse(*n));
        prims.truncate(15);
        eprintln!("commonest primitives: {prims:?}");
        let mut callers: Vec<((&str, String), u64)> = PRIM_CALLERS.with(|c| std::mem::take(&mut *c.borrow_mut())).into_iter().collect();
        callers.sort_by_key(|(_, n)| std::cmp::Reverse(*n));
        callers.truncate(30);
        for ((p, w), n) in callers {
            eprintln!("  {n:>8} {p} from {w}");
        }
    }
}

thread_local! {
    static CALLOUTS: std::cell::RefCell<[u64; ROUTINES.len()]> = const { std::cell::RefCell::new([0; ROUTINES.len()]) };
    static CALLOUT_NANOS: std::cell::RefCell<[u64; ROUTINES.len()]> = const { std::cell::RefCell::new([0; ROUTINES.len()]) };
    static ROUND_TRIP_WORDS: std::cell::RefCell<u64> = const { std::cell::RefCell::new(0) };
    /// Words of stack captured into continuations, and how many there were.
    pub(crate) static CAPTURED: std::cell::RefCell<(u64, u64)> = const { std::cell::RefCell::new((0, 0)) };
    static PRIM_COUNTS: std::cell::RefCell<std::collections::HashMap<&'static str, u64>> = std::cell::RefCell::new(std::collections::HashMap::new());
    /// The same, by the word each call is made from.
    static PRIM_CALLERS: std::cell::RefCell<std::collections::HashMap<(&'static str, String), u64>> = std::cell::RefCell::new(std::collections::HashMap::new());
    /// Whether `FIXPT_CALLOUTS` is set, asked once.
    pub(crate) static TIMING: bool = std::env::var_os("FIXPT_CALLOUTS").is_some();
    /// A runtime primitive's message, when one failed in a call-out: a
    /// trap's code cannot carry it.
    static LAST_MESSAGE: std::cell::RefCell<Option<String>> = const { std::cell::RefCell::new(None) };
}

/// The heap the state's run holds: the runtime's, or the bare heap's.
///
/// # Safety
/// `st` is a running machine's state (see `callout`).
unsafe fn heap_of<'a>(st: &State) -> &'a mut Heap {
    if st.rt != 0 {
        // SAFETY: the runtime `run_in_runtime` holds exclusively.
        unsafe { &mut (*(st.rt as *mut fixpt_runtime::Runtime)).heap }
    } else {
        // SAFETY: the heap `run` holds exclusively.
        unsafe { &mut *(st.heap as *mut Heap) }
    }
}

/// Run routine `n` with the Rust machine on these stacks: lift them into
/// one (the words are laid out alike, so this is only reordering), run the
/// routine, and put them back. Costs the stacks' size, so it is for the
/// routines too rare, or too involved, to have machine code of their own.
fn round_trip(st: &mut State, n: u64) -> Result<(), Trap> {
    use fixpt_engine::cellular::{Machine, Snapshot};
    let nds = (st.ds_base - st.dsp) as usize / 8;
    let nentries = (st.rs_base - st.rsp) as usize / 32;
    // SAFETY: the machine's stacks, between their pointers and bases.
    let word = |a: u64| unsafe { Value(*(a as *const u64)) };
    let ds: Vec<Value> = (0..nds).map(|i| word(st.ds_base - 8 - 8 * i as u64)).collect();
    let mut rs = Vec::with_capacity(4 * nentries);
    for e in 0..nentries {
        let at = st.rs_base - 32 * (e as u64 + 1);
        for j in 0..4 {
            rs.push(word(at + 8 * j));
        }
    }
    if TIMING.with(|t| *t) {
        ROUND_TRIP_WORDS.with(|w| *w.borrow_mut() += (nds + 4 * nentries) as u64);
    }
    let mut at = Snapshot { cur: Value(st.cur), k: (st.d / 8) as usize, fp: (st.fp / 8) as usize, clo: Value(st.clo) };
    let mut m = Machine::from_stacks(ds, rs);
    let result = if st.rt != 0 {
        // SAFETY: the runtime `run_in_runtime` holds exclusively.
        let rt = unsafe { &mut *(st.rt as *mut fixpt_runtime::Runtime) };
        m.run_routine(rt, n as i64, &mut at)
    } else {
        // SAFETY: the heap `run` holds exclusively.
        let heap = unsafe { &mut *(st.heap as *mut Heap) };
        m.run_routine_on_heap(heap, n as i64, &mut at)
    };
    let (ds, rs) = m.into_stacks();
    // SAFETY: within the stacks' room: the Rust machine checks the same
    // limits the native one does.
    let put = |a: u64, v: Value| unsafe { *(a as *mut u64) = v.raw() };
    for (i, v) in ds.iter().enumerate() {
        put(st.ds_base - 8 - 8 * i as u64, *v);
    }
    st.dsp = st.ds_base - 8 * ds.len() as u64;
    for (e, chunk) in rs.chunks(4).enumerate() {
        let at = st.rs_base - 32 * (e as u64 + 1);
        for (j, v) in chunk.iter().enumerate() {
            put(at + 8 * j as u64, *v);
        }
    }
    st.rsp = st.rs_base - 8 * rs.len() as u64;
    st.cur = at.cur.raw();
    st.d = 8 * at.k as u64;
    st.fp = 8 * at.fp as u64;
    st.clo = at.clo.raw();
    result
}

/// `prim p n`: runtime primitive `p` on the top `n` values, in place. The
/// stacks are roots as they lie: a return entry's `d` and frame pointer
/// have a fixnum's bits.
fn prim(st: &mut State) -> Result<(), Trap> {
    let name = "prim";
    if st.rt == 0 {
        return Err(Trap::Prim("no runtime to call a primitive in".into()));
    }
    // SAFETY: the runtime `run_in_runtime` holds exclusively.
    let rt = unsafe { &mut *(st.rt as *mut fixpt_runtime::Runtime) };
    let k = (st.d / 8) as usize;
    let p = rt.heap.bloblet_slot(Value(st.cur), k).as_fixnum() as usize;
    let count = rt.heap.bloblet_slot(Value(st.cur), k + 1).as_fixnum() as usize;
    let depth = (st.ds_base - st.dsp) as usize / 8;
    if depth < count {
        return Err(Trap::Underflow { routine: name });
    }
    if count == 0 && st.dsp - 8 < st.ds_limit {
        return Err(Trap::StackOverflow);
    }
    let Some(def) = fixpt_runtime::PRIMITIVES.get(p) else { return Err(Trap::Prim(format!("no primitive {p}"))) };
    if TIMING.with(|t| *t) {
        PRIM_COUNTS.with(|c| *c.borrow_mut().entry(def.name).or_insert(0) += 1);
        let caller = rt.heap.symbol_name(rt.heap.bloblet_slot(Value(st.cur), WORD_NAME));
        PRIM_CALLERS.with(|c| *c.borrow_mut().entry((def.name, caller)).or_insert(0) += 1);
    }
    let fixpt_runtime::PrimKind::Simple(f) = def.kind else { return Err(Trap::Prim(format!("`{}` needs an engine", def.name))) };
    if count < def.min || def.max.is_some_and(|m| count > m) {
        return Err(Trap::Prim(format!("`{}` given {count} argument(s)", def.name)));
    }
    safepoint(st, &mut rt.heap);
    // The top is at `dsp`; the arguments go deepest first.
    // SAFETY: as above.
    let word = |a: u64| unsafe { Value(*(a as *const u64)) };
    // On the stack, for as many as most primitives take.
    let (mut buf, mut many) = ([Value::NULL; 8], Vec::new());
    let args: &mut [Value] = if count <= buf.len() {
        for (k, i) in (0..count).rev().enumerate() {
            buf[k] = word(st.dsp + 8 * i as u64);
        }
        &mut buf[..count]
    } else {
        many.extend((0..count).rev().map(|i| word(st.dsp + 8 * i as u64)));
        &mut many[..]
    };
    let v = f(rt, args).map_err(|t| Trap::Prim(fixpt_engine::cellular::describe(rt, t.obj)))?;
    st.dsp = st.dsp + 8 * count as u64 - 8;
    // SAFETY: the slot the arguments had, or one checked above.
    unsafe { *(st.dsp as *mut u64) = v.raw() };
    st.d += 16;
    Ok(())
}

/// A safepoint, as in the Rust machine: the stacks are roots as they lie,
/// with the word running and the closure.
fn safepoint(st: &mut State, heap: &mut Heap) {
    let (nds, nrs) = ((st.ds_base - st.dsp) as usize / 8, (st.rs_base - st.rsp) as usize / 8);
    // SAFETY: the machine's stacks, between their pointers and bases, every
    // word a value.
    let ds = unsafe { std::slice::from_raw_parts_mut(st.dsp as *mut Value, nds) };
    let rs = unsafe { std::slice::from_raw_parts_mut(st.rsp as *mut Value, nrs) };
    let mut regs = [Value(st.cur), Value(st.clo)];
    heap.maybe_collect(&mut [ds, rs, &mut regs]);
    (st.cur, st.clo) = (regs[0].raw(), regs[1].raw());
}

/// `closure w n`: a closure of word `w` over the top `n` values, which it
/// replaces. Needs only the top of the stack, so no round trip.
fn closure(st: &mut State) -> Result<(), Trap> {
    use fixpt_heap::layout::cellular::{CLOSURE_FREE0, CLOSURE_WORD};
    // SAFETY: the heap the state's run holds.
    let heap = unsafe { heap_of(st) };
    safepoint(st, heap);
    let k = (st.d / 8) as usize;
    let w = heap.bloblet_slot(Value(st.cur), k);
    let count = heap.bloblet_slot(Value(st.cur), k + 1).as_fixnum() as usize;
    let depth = (st.ds_base - st.dsp) as usize / 8;
    if depth < st.fp as usize / 8 + count {
        return Err(Trap::Underflow { routine: "closure" });
    }
    if count == 0 && st.dsp - 8 < st.ds_limit {
        return Err(Trap::StackOverflow);
    }
    let c = heap.make_bloblet(fixpt_heap::layout::kind("cellular-closure"), count + 1, 0, true);
    heap.set_bloblet_slot(c, CLOSURE_WORD, w);
    // SAFETY: the machine's data stack; the top is at `dsp`, the free
    // values deepest first.
    let word = |a: u64| unsafe { Value(*(a as *const u64)) };
    for i in 0..count {
        heap.set_bloblet_slot(c, CLOSURE_FREE0 + i, word(st.dsp + 8 * (count - 1 - i) as u64));
    }
    st.dsp = st.dsp + 8 * count as u64 - 8;
    // SAFETY: a slot the free values had, or one checked above.
    unsafe { *(st.dsp as *mut u64) = c.raw() };
    st.d += 16;
    st.base = 0;
    st.alloc_limit = heap.inline_limit() as u64;
    Ok(())
}

/// The routine, on the stacks as slices (top first). Returns how many
/// values to pop; any result goes in the slot that will be the new top.
fn callout_routine(heap: &mut Heap, st: &mut State, ds: &mut [Value], rs: &mut [Value], name: &'static str) -> Result<usize, Trap> {
    let underflow = Trap::Underflow { routine: name };
    let field = Trap::Field { routine: name };
    match name {
        "field@" => {
            let [k, obj, ..] = *ds else { return Err(underflow) };
            // The fast path has checked the types.
            let k = usize::try_from(k.as_fixnum()).map_err(|_| field.clone())?;
            ds[1] = heap.bloblet_field(obj, k).map_err(|_| field)?;
            Ok(1)
        }
        "field!" => {
            let [k, obj, x, ..] = *ds else { return Err(underflow) };
            if !k.is_fixnum() || !obj.is_bloblet() {
                return Err(Trap::Type { routine: name });
            }
            let k = usize::try_from(k.as_fixnum()).map_err(|_| field.clone())?;
            heap.set_bloblet_field(obj, k, x).map_err(|_| field)?;
            Ok(3)
        }
        "cons" => {
            if ds.len() < 2 {
                return Err(underflow);
            }
            let mut regs = [Value(st.cur), Value(st.clo)];
            heap.maybe_collect(&mut [ds, rs, &mut regs]);
            st.cur = regs[0].raw();
            st.clo = regs[1].raw();
            let p = heap.cons(ds[1], ds[0]);
            ds[1] = p;
            Ok(1)
        }
        other => unreachable!("{other} is not a callout"),
    }
}

/// A stack in memory of its own: `room` bytes below the base, a guard below
/// that, and a guard of `above` bytes above the base.
struct Stack {
    map: *mut u8,
    len: usize,
    base: u64,
}

impl Stack {
    fn new(room: usize, above: usize) -> Stack {
        let p = page();
        let guard_lo = p;
        let room = room.div_ceil(p) * p;
        let above = above.div_ceil(p) * p;
        let len = guard_lo + room + above;
        // SAFETY: a fresh private mapping, inaccessible until the room in
        // the middle is opened.
        let map = unsafe {
            libc::mmap(std::ptr::null_mut(), len, libc::PROT_NONE, libc::MAP_PRIVATE | libc::MAP_ANON, -1, 0)
        };
        assert!(map != libc::MAP_FAILED, "cannot map a stack: {}", std::io::Error::last_os_error());
        // SAFETY: the middle of the mapping just made.
        let r = unsafe {
            libc::mprotect((map as *mut u8).add(guard_lo) as *mut _, room, libc::PROT_READ | libc::PROT_WRITE)
        };
        assert!(r == 0, "cannot open a stack: {}", std::io::Error::last_os_error());
        Stack { map: map as *mut u8, len, base: map as u64 + (guard_lo + room) as u64 }
    }
}

impl Drop for Stack {
    fn drop(&mut self) {
        // SAFETY: the mapping made in `new`.
        unsafe { libc::munmap(self.map as *mut _, self.len) };
    }
}

fn page() -> usize {
    // SAFETY: no preconditions.
    unsafe { libc::sysconf(libc::_SC_PAGESIZE) as usize }
}

/// A machine's two stacks, and how a run starts and ends on them: the part
/// every native machine shares.
pub(crate) struct Stacks {
    ds: Stack,
    rs: Stack,
}

/// The most cells a word can have, so the most one word's straight-line code
/// can push or pop between the machine's checks.
const MAX_CELLS: usize = 1 << 18;

impl Stacks {
    pub(crate) fn new() -> Stacks {
        Stacks { ds: Stack::new(8 * (DS_LIMIT + MAX_CELLS), 8 * MAX_CELLS), rs: Stack::new(32 * (RS_LIMIT + 2), page()) }
    }

    /// The state to start `word` in, with `args` on the data stack (the last
    /// on top). The heap must stay exclusively the machine's until the run
    /// ends.
    pub(crate) fn start(&mut self, heap: &mut Heap, word: Value, args: &[Value], fuel: u64) -> State {
        assert!(fixpt_engine::cellular::is_word(heap, word), "{word:?} is not a cellular word");
        let entry = heap.bloblet_slot(word, WORD_ENTRY).as_fixnum() as u64;
        assert!(entry == ROUTINE_DOCOL || entry >= PRIMITIVES as u64, "the machine starts with a word made of cells");
        assert!(args.len() <= DS_LIMIT);
        let dsp = self.ds.base - 8 * args.len() as u64;
        for (i, a) in args.iter().rev().enumerate() {
            // SAFETY: inside the data stack's room, just below its base.
            unsafe { *((dsp + 8 * i as u64) as *mut u64) = a.raw() };
        }
        State {
            base: 0,
            words: heap.words_address() as u64,
            cur: Value::FALSE.raw(),
            d: 0,
            dsp,
            rsp: self.rs.base,
            table: 0,
            fal: Value::FALSE.raw(),
            tru: Value::TRUE.raw(),
            fuel: fuel.max(1),
            status: 0,
            aux: 0,
            callout: callout as *const () as u64,
            start: word.raw(),
            heap: heap as *mut Heap as u64,
            ds_base: self.ds.base,
            rs_base: self.rs.base,
            ds_limit: self.ds.base - 8 * DS_LIMIT as u64,
            // Slot 0 is where the next value will go: the frame the
            // arguments are, as the Rust machine starts.
            fp: 8 * args.len() as u64,
            clo: Value::FALSE.raw(),
            rt: 0,
            rs_limit: self.rs.base - 32 * (RS_LIMIT as u64 + 1),
            routines: [0; ROUTINE_SLOTS],
            trap: 0,
            exit: 0,
            resume: 0,
            top: heap.top_address() as u64,
            alloc_limit: heap.inline_limit() as u64,
            regions: heap.region_table_address() as u64,
            cards: heap.card_table_address() as u64,
            leaf_link: 0,
            pure: pure_call as *const () as u64,
        }
    }

    /// What a run that stopped in `st` produced: the data stack, bottom
    /// first, or its trap.
    pub(crate) fn finish(&self, st: &State) -> Result<Vec<Value>, Trap> {
        if st.status != 0 {
            let t = Trap::from_code(st.status, st.aux);
            if let Trap::Prim(_) = t
                && let Some(m) = LAST_MESSAGE.with(|c| c.borrow_mut().take())
            {
                return Err(Trap::Prim(m));
            }
            return Err(t);
        }
        let n = (self.ds.base - st.dsp) as usize / 8;
        // SAFETY: the machine's data stack, from its pointer to its base.
        let ds = unsafe { std::slice::from_raw_parts(st.dsp as *const Value, n) };
        Ok(ds.iter().rev().copied().collect())
    }
}

/// Entry numbers from `PRIMITIVES` up name words compiled to machine code,
/// numbered across every machine in the process, so that no two words share
/// one. A machine that has no code for a word's number runs its cells.
pub const NATIVE_SLOTS: usize = 1 << 16;
static NEXT_SLOT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(PRIMITIVES);

/// Each installed code's machine code, by native slot: where it runs, and
/// how many instructions. For showing it (`,disassemble-asm`), which is
/// asked for from inside a machine's run, and so cannot reach the machine.
/// A machine's entries go when it does.
static CODE_OF_SLOT: std::sync::Mutex<std::collections::BTreeMap<usize, (usize, usize)>> =
    std::sync::Mutex::new(std::collections::BTreeMap::new());

/// Word `word`'s machine code, shown an instruction a line, if a native
/// machine has compiled it: for a word run as register code, the adapter
/// into it (its register word shows its own).
pub fn machine_code_text(heap: &Heap, word: Value) -> Option<String> {
    let slot = heap.bloblet_slot(word, WORD_ENTRY).as_fixnum();
    if slot < PRIMITIVES as i64 {
        return None;
    }
    let (at, n) = *CODE_OF_SLOT.lock().expect("not poisoned").get(&(slot as usize))?;
    // SAFETY: the record is of code a live machine installed and flushed,
    // `n` instructions at `at`, in its code space's read+execute view,
    // which is readable, and stays mapped while the machine lives; its
    // records go when it does.
    let code = unsafe { std::slice::from_raw_parts(at as *const u32, n) };
    let mut out = format!("machine code, {n} instructions at {at:#x} (native slot {slot}):\n");
    for (i, w) in code.iter().enumerate() {
        out.push_str(&format!("  {i:>5}: {w:08x}  {}\n", crate::arm64::disasm::disassemble(*w, i as i64)));
    }
    Some(out)
}

/// Room for the machine and for the words compiled into it: reserved, not
/// committed, so it costs address space until used. Collecting the code
/// copies what is live into a second space for the while.
const CODE_SPACE: usize = 256 << 20;

/// The native machine: its code, generated once, the words compiled into
/// it, and its stacks.
pub struct NativeMachine {
    space: CodeSpace,
    entry: Offset,
    /// Where the machine's code is, and in it the common trap and exit.
    machine_at: Offset,
    commons: [i64; 2],
    /// Each entry number's code: a routine's, a compiled word's entry as a
    /// cell, or, for a number this machine has no code for, `docol`'s.
    table: Vec<u64>,
    /// Each entry number's table of where its code resumes, by `8k`, or 0.
    resume: Vec<u64>,
    stacks: Stacks,
    /// Fuel left after the last run.
    pub fuel_left: u64,
    /// The native slots this machine has installed code in.
    slots: Vec<usize>,
    /// How many instructions the machine's own code is.
    machine_len: usize,
    /// Each word compiled into this machine, for [`collect_code`]
    /// (NativeMachine::collect_code) to keep, moved, or let go.
    installed: Vec<Installed>,
    /// Native slots let go, for reuse.
    free_slots: Vec<usize>,
    /// Bytes of code installed since the code was last collected, and the
    /// bytes live after that collection: when the first passes both
    /// [`CODE_COLLECT_BYTES`] and the second, the code is collected again
    /// (as Larceny's code space is: `0524c5d6` in its repository).
    since_collect: usize,
    live_after: usize,
    /// Words compiled into this machine so far.
    compiled: usize,
}

/// Code installed past which, and past what was live, the code is collected.
pub const CODE_COLLECT_BYTES: usize = 8 << 20;

/// A word compiled into a machine: its slot, a weak reference to it in its
/// heap (which heap, by [`Heap::serial`]), and where its code and its table
/// of where to resume are, in bytes.
struct Installed {
    /// Which word this was compiled, in order, in this machine.
    seq: usize,
    slot: usize,
    heap: u64,
    weak: usize,
    code: (Offset, usize),
    resume: (Offset, usize),
    /// What it is, for a fault or a profiler to say (`crate::symbols`).
    name: String,
}

impl Drop for NativeMachine {
    fn drop(&mut self) {
        let mut code = CODE_OF_SLOT.lock().expect("not poisoned");
        for s in &self.slots {
            code.remove(s);
        }
    }
}

impl NativeMachine {
    pub fn new() -> NativeMachine {
        let (code, entry, starts, commons) = generate();
        let mut space = CodeSpace::new(CODE_SPACE).expect("a code space");
        let at = space.alloc(code.len() * 4, 16).expect("room for the machine");
        space.write_code(at, &code);
        space.flush(at, code.len() * 4);
        let mut table: Vec<u64> = starts.iter().map(|s| space.exec_addr(at + 4 * s) as u64).collect();
        let docol = table[ROUTINE_DOCOL as usize];
        table.resize(NATIVE_SLOTS, docol);
        let resume = vec![0; NATIVE_SLOTS];
        let m = NativeMachine {
            entry: at + 4 * entry,
            machine_at: at,
            commons,
            space,
            table,
            resume,
            stacks: Stacks::new(),
            fuel_left: 0,
            slots: Vec::new(),
            machine_len: code.len(),
            installed: Vec::new(),
            free_slots: Vec::new(),
            since_collect: 0,
            live_after: 0,
            compiled: 0,
        };
        m.note_machine();
        m
    }

    /// The machine's own code, named for profilers (`crate::symbols`):
    /// its entry and common exits, then each routine, by name.
    fn note_machine(&self) {
        if !crate::symbols::enabled() {
            return;
        }
        let start = self.space.exec_addr(self.machine_at) as u64;
        let end = start + 4 * self.machine_len as u64;
        let first = self.table[0];
        crate::symbols::note(start as usize, (first - start) as usize, "cellular machine: entry and exits");
        for (n, (name, _)) in ROUTINES.iter().enumerate() {
            let from = self.table[n];
            let to = ROUTINES.get(n + 1).map_or(end, |_| self.table[n + 1]);
            crate::symbols::note(from as usize, (to - from) as usize, &format!("cellular machine: {name}"));
        }
    }

    /// Whether so much code has been installed since the code was last
    /// collected that it should be again.
    pub fn code_collection_due(&self) -> bool {
        self.since_collect > CODE_COLLECT_BYTES.max(self.live_after)
    }

    /// Bytes of code space in use.
    pub fn code_used(&self) -> usize {
        self.space.used()
    }

    /// Collect the code: into a fresh space, the machine's own code and each
    /// word compiled into it that is still alive, as `heap`'s last collection
    /// found; the space they were in let go. A word's code refers to nothing
    /// outside itself by address (it reaches the machine's trap and exit
    /// through the state, and other words through the table), so it is moved
    /// as it is; what refers to it by address is moved on: its slot's entry
    /// in the table, and its table of where to resume. A word that died lets
    /// its slot go. Only between runs: no return address or ip may point
    /// into the old space. A word of another heap than `heap` is kept.
    pub fn collect_code(&mut self, heap: &mut Heap) -> Result<(), String> {
        let (started, before, words) = (std::time::Instant::now(), self.space.used(), self.installed.len());
        let mut new = CodeSpace::new(CODE_SPACE).map_err(|e| format!("a code space: {e}"))?;
        let old_exec = |space: &CodeSpace, at: Offset| space.exec_addr(at) as u64;
        // The machine's own code, its routines' entries moved with it.
        let len = 4 * self.machine_len;
        let m_at = new.alloc(len, 16).ok_or("the code space is full")?;
        new.write(m_at, self.space.bytes(self.machine_at, len));
        let (lo, hi) = (old_exec(&self.space, self.machine_at), old_exec(&self.space, self.machine_at) + len as u64);
        let delta = old_exec(&new, m_at).wrapping_sub(lo);
        for e in self.table.iter_mut() {
            if (lo..hi).contains(e) {
                *e = e.wrapping_add(delta);
            }
        }
        self.entry = self.entry - self.machine_at + m_at;
        self.machine_at = m_at;
        let docol = self.table[ROUTINE_DOCOL as usize];
        // `FIXPT_CODE_TRACE_SEQ=N`: why the first word compiled at or after
        // the Nth that is still alive is: for finding what keeps code.
        if let Some(n) = std::env::var("FIXPT_CODE_TRACE_SEQ").ok().and_then(|n| n.parse::<usize>().ok())
            && let Some((w, v)) = self.installed.iter().filter(|w| w.seq >= n && w.heap == heap.serial()).find_map(|w| {
                let v = heap.weak_get(w.weak)?;
                let name = std::env::var("FIXPT_CODE_TRACE_NAME").unwrap_or_default();
                heap.describe(v).contains(&name).then_some((w, v))
            })
        {
            eprintln!("; word {} ({}) is alive:", w.seq, heap.describe(v));
            for step in heap.path_to(v, &[]).unwrap_or_else(|| vec!["(not reached from the heap's roots)".into()]) {
                eprintln!(";   {step}");
            }
        }
        let mut code_of = CODE_OF_SLOT.lock().expect("not poisoned");
        let mut kept = Vec::with_capacity(self.installed.len());
        for w in std::mem::take(&mut self.installed) {
            if w.heap == heap.serial() && heap.weak_get(w.weak).is_none() {
                heap.weak_release(w.weak);
                self.table[w.slot] = docol;
                self.resume[w.slot] = 0;
                code_of.remove(&w.slot);
                self.slots.retain(|s| *s != w.slot);
                self.free_slots.push(w.slot);
                continue;
            }
            let at = new.alloc(w.code.1, 32).ok_or("the code space is full")?;
            new.write(at, self.space.bytes(w.code.0, w.code.1));
            let delta = old_exec(&new, at).wrapping_sub(old_exec(&self.space, w.code.0));
            let rt_at = new.alloc(w.resume.1, 8).ok_or("the code space is full")?;
            for k in (0..w.resume.1).step_by(8) {
                let v = self.space.read_u64(w.resume.0 + k);
                new.write_u64(rt_at + k, if v == 0 { 0 } else { v.wrapping_add(delta) });
            }
            self.table[w.slot] = old_exec(&new, at);
            self.resume[w.slot] = old_exec(&new, rt_at);
            code_of.insert(w.slot, (new.exec_addr(at), w.code.1 / 4));
            crate::faults::note(new.exec_addr(at), w.code.1, w.name.clone());
            kept.push(Installed { code: (at, w.code.1), resume: (rt_at, w.resume.1), ..w });
        }
        drop(code_of);
        new.flush(0, new.used());
        self.installed = kept;
        self.space = new;
        self.note_machine();
        self.since_collect = 0;
        self.live_after = self.space.used();
        if std::env::var_os("FIXPT_CODE_TRACE").is_some() {
            eprintln!(
                "; code collected: {} words of {} kept, {} KB of {} KB, in {:.1} ms",
                self.installed.len(),
                words,
                self.live_after >> 10,
                before >> 10,
                started.elapsed().as_secs_f64() * 1e3
            );
        }
        Ok(())
    }

    /// Compile `word`'s cells to machine code in this machine, and make the
    /// word's entry name it (step 11a). The code does what the cells do,
    /// routine for routine, with the ip kept in step, so that it and
    /// cellular code mix freely; branches become jumps, and the dispatch
    /// between cells goes. A word already compiled is left alone.
    pub fn compile_word(&mut self, heap: &mut Heap, word: Value) -> Result<(), String> {
        let entry = heap.bloblet_slot(word, WORD_ENTRY).as_fixnum() as u64;
        if entry != ROUTINE_DOCOL {
            return if entry >= PRIMITIVES as u64 { Ok(()) } else { Err("not a word made of cells".into()) };
        }
        // Assembled once for its size, which does not depend on where it goes.
        let (code, _) = assemble_word(heap, word, [0, 0])?;
        let (at, far) = self.reserve_collecting(heap, code.len())?;
        let (code, starts) = assemble_word(heap, word, far)?;
        self.install(heap, word, at, &code, &starts)
    }

    /// [`reserve`](Self::reserve), collecting the code first if there is no
    /// room: the words dead at the heap's last collection give theirs back.
    pub fn reserve_collecting(&mut self, heap: &mut Heap, len: usize) -> Result<(Offset, [i64; 2]), String> {
        match self.reserve(len) {
            Ok(r) => Ok(r),
            Err(_) => {
                self.collect_code(heap)?;
                self.reserve(len)
            }
        }
    }

    /// Room for `len` instructions: where, and where the machine's common
    /// trap and exit are from there, in instructions, for [`assemble_word`].
    pub fn reserve(&mut self, len: usize) -> Result<(Offset, [i64; 2]), String> {
        let at = self.space.alloc(4 * len, 32).ok_or("the code space is full")?;
        let origin = (at - self.machine_at) as i64 / 4;
        Ok((at, [self.commons[0] - origin, self.commons[1] - origin]))
    }

    /// Place `code`, assembled for `at` (from [`reserve`](Self::reserve)),
    /// and make `word`'s entry name it. `starts[i]` is where cell `i`'s
    /// code starts, in instructions, or -1 if no instruction starts there.
    pub fn install(&mut self, heap: &mut Heap, word: Value, at: Offset, code: &[u32], starts: &[i64]) -> Result<(), String> {
        let fields = heap.bloblet_head(word).fields;
        if starts.len() != fields + 1 - WORD_CELL0 {
            return Err(format!("{} starts for {} cells", starts.len(), fields + 1 - WORD_CELL0));
        }
        self.space.write_code(at, code);
        self.space.flush(at, 4 * code.len());
        let what = format!("{} {}", if heap.is_register_word(word) { "register word" } else { "word" }, heap.symbol_name(heap.bloblet_slot(word, WORD_NAME)));
        crate::faults::note(self.space.exec_addr(at), 4 * code.len(), what.clone());
        // Where to resume, by k: each instruction's start.
        let table_len = fields + 2;
        let rt_at = self.space.alloc(8 * table_len, 8).ok_or("the code space is full")?;
        for k in 0..table_len {
            let ins = k.checked_sub(WORD_CELL0).and_then(|i| starts.get(i)).copied().unwrap_or(-1);
            let v = if ins < 0 { 0 } else { self.space.exec_addr(at + 4 * ins as usize) as u64 };
            self.space.write_u64(rt_at + 8 * k, v);
        }
        let slot = match self.free_slots.pop() {
            Some(s) => s,
            None => NEXT_SLOT.fetch_add(1, std::sync::atomic::Ordering::Relaxed),
        };
        if slot >= NATIVE_SLOTS {
            return Err("no native slots left".into());
        }
        self.table[slot] = self.space.exec_addr(at) as u64;
        self.resume[slot] = self.space.exec_addr(rt_at) as u64;
        CODE_OF_SLOT.lock().expect("not poisoned").insert(slot, (self.space.exec_addr(at), code.len()));
        self.slots.push(slot);
        heap.set_bloblet_slot(word, WORD_ENTRY, Value::fixnum(slot as i64));
        let weak = heap.weak_add(word);
        self.compiled += 1;
        self.installed.push(Installed { seq: self.compiled, slot, heap: heap.serial(), weak, code: (at, 4 * code.len()), resume: (rt_at, 8 * table_len), name: what });
        self.since_collect += 4 * code.len() + 8 * table_len;
        Ok(())
    }

    /// Compile `word` and every word it can reach through its cells and
    /// operands: words called, closures made, literals.
    pub fn compile_reachable(&mut self, heap: &mut Heap, word: Value) -> Result<usize, String> {
        self.compile_reachable_as(heap, word, false)
    }

    /// [`compile_reachable`](Self::compile_reachable), with each word that
    /// has register code (PLAN.md 13h′) run as register code when
    /// `registers`, and everything its register code reaches compiled too.
    pub fn compile_reachable_as(&mut self, heap: &mut Heap, word: Value, registers: bool) -> Result<usize, String> {
        if self.code_collection_due() {
            self.collect_code(heap)?;
        }
        let closure = kind("cellular-closure");
        let (mut todo, mut seen, mut n) = (vec![word], std::collections::HashSet::new(), 0);
        while let Some(w) = todo.pop() {
            if !seen.insert(w.raw()) {
                continue;
            }
            let entry = heap.bloblet_slot(w, WORD_ENTRY).as_fixnum() as u64;
            if entry != ROUTINE_DOCOL && entry < PRIMITIVES as u64 {
                continue;
            }
            // The word `%run-word` made to call a closure is run once, as
            // cells: compiled, it would hold code space and a slot for good.
            // Only the closure it calls is code; the rest of its operands
            // are the arguments, data, though they may be words.
            let fields = heap.bloblet_head(w).fields;
            if w == word && heap.symbol_name(heap.bloblet_slot(w, WORD_NAME)) == fixpt_runtime::prim::CALL_CLOSURE {
                // `… lit closure call n exit`
                todo.push(heap.bloblet_slot(heap.bloblet_slot(w, fields - 3), CLOSURE_WORD));
                continue;
            }
            for k in WORD_CELL0..=fields {
                let v = heap.bloblet_slot(w, k);
                if heap.is_cellular_word(v) {
                    todo.push(v);
                } else if v.is_bloblet() && heap.bloblet_kind(v) == closure {
                    todo.push(heap.bloblet_slot(v, CLOSURE_WORD));
                }
            }
            if entry == ROUTINE_DOCOL {
                let twin = heap.bloblet_slot(w, fixpt_heap::layout::cellular::WORD_TWIN);
                if registers && heap.is_register_word(twin) {
                    for k in WORD_CELL0..=heap.bloblet_head(twin).fields {
                        let v = heap.bloblet_slot(twin, k);
                        if heap.is_cellular_word(v) {
                            todo.push(v);
                        }
                    }
                    self.compile_register_word(heap, w)?;
                } else {
                    self.compile_word(heap, w)?;
                }
                n += 1;
            }
        }
        Ok(n)
    }

    /// The machine's own code, its routines and its entry, as instructions:
    /// for looking at, and for checking the disassembler reads all of it.
    pub fn machine_instructions(&self) -> Vec<u32> {
        (0..self.machine_len).map(|i| self.space.read_u32(self.machine_at + 4 * i)).collect()
    }

    /// Where this machine's common trap and exit are, for the state.
    fn commons_addresses(&self) -> (u64, u64) {
        let at = |i: i64| self.space.exec_addr(self.machine_at + 4 * i as usize) as u64;
        (at(self.commons[0]), at(self.commons[1]))
    }

    /// The machine code, for looking at.
    pub fn code_bytes(&self) -> usize {
        self.space.used()
    }

    /// Run `word`, which must be made of cells, with `args` on the data stack
    /// (the last on top), for at most `fuel` word entries and taken
    /// branches. Returns the data stack, bottom first.
    pub fn run(&mut self, heap: &mut Heap, word: Value, args: &[Value], fuel: u64) -> Result<Vec<Value>, Trap> {
        let mut st = self.stacks.start(heap, word, args, fuel);
        st.table = self.table.as_ptr() as u64;
        st.resume = self.resume.as_ptr() as u64;
        (st.trap, st.exit) = self.commons_addresses();
        // SAFETY: the entry follows the C convention and takes the state.
        // Everything the machine touches is valid while it runs: the state,
        // the table and the stacks here, and the heap, which `heap` holds
        // exclusively and which the machine reaches only through the state.
        // Words are frozen and their cells checked when built, so every cell
        // it runs is a primitive or a word.
        unsafe { self.space.call(self.entry, [&mut st as *mut State as u64, 0, 0, 0]) };
        self.fuel_left = st.fuel;
        self.stacks.finish(&st)
    }

    /// The same in a runtime, whose primitives the routines this machine
    /// hands to the Rust machine (`prim` and the rest) call.
    pub fn run_in_runtime(
        &mut self,
        rt: &mut fixpt_runtime::Runtime,
        word: Value,
        args: &[Value],
        fuel: u64,
    ) -> Result<Vec<Value>, Trap> {
        let rt_ptr = rt as *mut fixpt_runtime::Runtime as u64;
        let mut st = self.stacks.start(&mut rt.heap, word, args, fuel);
        st.rt = rt_ptr;
        st.table = self.table.as_ptr() as u64;
        st.resume = self.resume.as_ptr() as u64;
        (st.trap, st.exit) = self.commons_addresses();
        // SAFETY: as for `run`; the runtime, and so the heap, is reached
        // only through the state while the machine runs.
        unsafe { self.space.call(self.entry, [&mut st as *mut State as u64, 0, 0, 0]) };
        self.fuel_left = st.fuel;
        self.stacks.finish(&st)
    }
}

thread_local! {
    /// The machine `run_word` uses: one per thread, kept, so that the words
    /// compiled into it stay compiled.
    static MACHINE: std::cell::RefCell<Option<NativeMachine>> = const { std::cell::RefCell::new(None) };
}

/// Run `word` with `args` on a native machine in `rt`: what the runtime's
/// `%run-word` calls when a native machine is chosen (`Runtime::run_word`).
/// It runs the cells, with its routines as machine code;
/// [`run_word_compiled`] compiles every word it can reach first.
pub fn run_word(rt: &mut fixpt_runtime::Runtime, word: Value, args: &[Value]) -> Result<Value, String> {
    run_word_as(rt, word, args, false)
}

/// The same, compiling or not as `compile` says.
pub fn run_word_as(rt: &mut fixpt_runtime::Runtime, word: Value, args: &[Value], compile: bool) -> Result<Value, String> {
    MACHINE.with(|m| {
        // A run within a run (a primitive running a word) gets a machine
        // of its own, which compiles nothing.
        let Ok(mut m) = m.try_borrow_mut() else {
            let out = NativeMachine::new().run_in_runtime(rt, word, args, u64::MAX).map_err(|t| format!("{t:?}"));
            return out?.last().copied().ok_or_else(|| "the word left nothing".to_string());
        };
        let m = m.get_or_insert_with(NativeMachine::new);
        let (word, args) = collect_for_code(m, rt, word, args)?;
        if compile {
            m.compile_reachable(&mut rt.heap, word)?;
        }
        let fuel = rt.word_fuel;
        let out = m.run_in_runtime(rt, word, &args, fuel).map_err(|t| format!("{t:?}"));
        report_callouts();
        out?.last().copied().ok_or_else(|| "the word left nothing".to_string())
    })
}

/// Before running in `m`: if its code is due to be collected, first the
/// heap, so that the words that died are known to be dead (`word` and
/// `args` rooted, and moved on), then the code, here and not only as
/// compiling begins: a run that compiles nothing, of code placed from
/// elsewhere (`install`), would otherwise find it due at every run, and
/// collect the heap every time. Between runs of `m`, so no return address
/// points into its code. A heap whose collection is held off is left alone.
fn collect_for_code(m: &mut NativeMachine, rt: &mut fixpt_runtime::Runtime, word: Value, args: &[Value]) -> Result<(Value, Vec<Value>), String> {
    let mut word = [word];
    let mut args = args.to_vec();
    if m.code_collection_due() && !rt.heap.collection_inhibited() {
        rt.heap.collect(&mut [&mut word, &mut args]);
        m.collect_code(&mut rt.heap)?;
    }
    Ok((word[0], args))
}

/// [`run_word`], compiling what it runs, and running as register code
/// (PLAN.md 13h′) each word that has some.
pub fn run_word_registers(rt: &mut fixpt_runtime::Runtime, word: Value, args: &[Value]) -> Result<Value, String> {
    MACHINE.with(|m| {
        let Ok(mut m) = m.try_borrow_mut() else {
            let out = NativeMachine::new().run_in_runtime(rt, word, args, u64::MAX).map_err(|t| format!("{t:?}"));
            return out?.last().copied().ok_or_else(|| "the word left nothing".to_string());
        };
        let m = m.get_or_insert_with(NativeMachine::new);
        let (word, args) = collect_for_code(m, rt, word, args)?;
        m.compile_reachable_as(&mut rt.heap, word, true)?;
        let fuel = rt.word_fuel;
        let out = m.run_in_runtime(rt, word, &args, fuel).map_err(|t| format!("{t:?}"));
        report_callouts();
        out?.last().copied().ok_or_else(|| "the word left nothing".to_string())
    })
}

/// [`run_word`], never compiling: the words run as they are, compiled or not.
pub fn run_word_as_is(rt: &mut fixpt_runtime::Runtime, word: Value, args: &[Value]) -> Result<Value, String> {
    run_word_as(rt, word, args, false)
}

/// `f` on the machine [`run_word`] uses on this thread: to place code made
/// elsewhere into it, as the compiler written in FX-26 makes it. Not while
/// that machine runs.
pub fn with_machine<R>(f: impl FnOnce(&mut NativeMachine) -> R) -> R {
    MACHINE.with(|m| f(m.borrow_mut().get_or_insert_with(NativeMachine::new)))
}

/// Place `code`, a word's machine code made elsewhere (by the compiler
/// written in FX-26, `native.fx`), in the machine [`run_word`] uses on
/// this thread: the runtime's `place_code`. The code reaches the machine's
/// common trap and exit through the state, so it may go anywhere.
pub fn place_word(heap: &mut Heap, word: Value, code: &[u32], starts: &[i64]) -> Result<(), String> {
    with_machine(|m| {
        let (at, _) = m.reserve(code.len())?;
        m.install(heap, word, at, code, starts)
    })
}

/// [`run_word`], always compiling what it runs: for `%run-word`'s hook.
pub fn run_word_compiled(rt: &mut fixpt_runtime::Runtime, word: Value, args: &[Value]) -> Result<Value, String> {
    run_word_as(rt, word, args, true)
}

impl Default for NativeMachine {
    fn default() -> NativeMachine {
        NativeMachine::new()
    }
}
