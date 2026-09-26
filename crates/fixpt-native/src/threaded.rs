//! The native inner interpreter: the same threaded words the Rust bootstrap
//! interpreter runs (`fixpt_engine::threaded`), run by machine code written
//! into a code space with our own encoder.
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
use fixpt_engine::threaded::{DS_LIMIT, RS_LIMIT, Trap};
use fixpt_heap::layout::threaded::{KIND, PRIMITIVES, ROUTINE_DOCOL, ROUTINES, WORD_CELL0, WORD_ENTRY};
use fixpt_heap::layout::{H_FIELDS, T_DISTANCE};
use fixpt_heap::value::{TAG_BLOBLET, TAG_PAIR, TAG_TRAILER};
use fixpt_heap::{Heap, Value};
use std::mem::offset_of;

mod state {
    include!("state.rs");
}
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
const FAL: Reg = 26;
const TRU: Reg = 27;
const FUEL: Reg = 28;
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
    labels: Vec<Option<usize>>,
    fixups: Vec<(usize, usize)>,
    /// Traps raised in the routine being emitted, placed after it.
    stubs: Vec<(Label, u64, u64)>,
    trap_common: Label,
    exit_common: Label,
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
        self.labels[l.0] = Some(self.here());
    }
    fn to(&mut self, l: Label, w: u32) {
        self.fixups.push((self.here(), l.0));
        self.e(w);
    }
    fn b(&mut self, l: Label) {
        self.to(l, b(0));
    }
    fn b_cond(&mut self, c: Cond, l: Label) {
        self.to(l, b_cond(c, 0));
    }
    fn cbnz(&mut self, t: Reg, l: Label) {
        self.to(l, cbnz(t, 0));
    }
    fn cbz(&mut self, t: Reg, l: Label) {
        self.to(l, cbz(t, 0));
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
            let d = to as i64 - at as i64;
            let w = self.code[at];
            self.code[at] = if w & 0xFC00_0000 == 0x1400_0000 {
                b(d)
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
        self.e(ldr(FAL, ST, off(offset_of!(State, fal))));
        self.e(ldr(TRU, ST, off(offset_of!(State, tru))));
        self.e(ldr(FUEL, ST, off(offset_of!(State, fuel))));
    }

    fn fuel(&mut self) {
        self.e(subs_imm(FUEL, FUEL, 1));
        self.trap_if(Cond::Eq, Trap::OutOfFuel);
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
    /// unless it reports a trap.
    fn callout(&mut self, n: u64) {
        self.save();
        self.e(mov(0, ST));
        self.e(movz(1, n as u32, 0));
        self.e(ldr(X16, ST, off(offset_of!(State, callout))));
        self.e(blr(X16));
        let exit = self.exit_common;
        self.cbnz(0, exit);
        self.load();
        self.next();
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
fn generate() -> (Vec<u32>, usize, Vec<usize>) {
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
        let name: &'static str = name;
        match name {
            "docol" => {
                // x9 is the word and x11 its suffix + 4.
                a.fuel();
                a.ds_limit();
                a.rs_limit();
                a.e(add(X13, BASE, CUR));
                a.e(sub_imm(X13, X13, 4));
                a.e(sub(X13, X13, IP));
                a.e(stp_pre(CUR, X13, RSP, -16));
                a.e(mov(CUR, W));
                a.e(sub_imm(IP, X11, (4 + 8 * WORD_CELL0) as u32));
                a.next();
            }
            "exit" => {
                a.e(ldp_post(CUR, X13, RSP, 16));
                a.e(cmp(CUR, FAL));
                let ec = a.exit_common;
                a.b_cond(Cond::Eq, ec);
                a.e(add(IP, BASE, CUR));
                a.e(sub_imm(IP, IP, 4));
                a.e(sub(IP, IP, X13));
                a.next();
            }
            "halt" => {
                let ec = a.exit_common;
                a.b(ec);
            }
            "lit" => {
                a.e(ldr_post(X13, IP, -8));
                a.e(str_pre(X13, DSP, -8));
                a.next();
            }
            "branch" => {
                a.e(ldr_post(X13, IP, -8));
                a.e(sub(IP, IP, X13));
                a.fuel();
                a.ds_limit();
                a.next();
            }
            "0branch" => {
                let skip = a.label();
                a.e(ldr_post(X14, DSP, 8));
                a.e(ldr_post(X13, IP, -8));
                a.e(cmp(X14, FAL));
                a.b_cond(Cond::Ne, skip);
                a.e(sub(IP, IP, X13));
                a.fuel();
                a.ds_limit();
                a.bind(skip);
                a.next();
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
                a.next();
            }
            "drop" => {
                a.e(add_imm(DSP, DSP, 8));
                a.next();
            }
            "swap" => {
                a.e(ldp(X13, X14, DSP, 0));
                a.e(stp(X14, X13, DSP, 0));
                a.next();
            }
            "over" => {
                a.e(ldr(X13, DSP, 8));
                a.e(str_pre(X13, DSP, -8));
                a.next();
            }
            "+" | "-" => {
                a.two_fixnums(name);
                a.e(if name == "+" { adds(X15, X14, X13) } else { subs(X15, X14, X13) });
                a.trap_if(Cond::Vs, Trap::Overflow { routine: name });
                a.e(str_pre(X15, DSP, 8));
                a.next();
            }
            "<" => {
                a.two_fixnums(name);
                a.e(cmp(X14, X13));
                a.e(csel(X15, TRU, FAL, Cond::Lt));
                a.e(str_pre(X15, DSP, 8));
                a.next();
            }
            "eq" => {
                a.e(ldp(X13, X14, DSP, 0));
                a.e(cmp(X14, X13));
                a.e(csel(X15, TRU, FAL, Cond::Eq));
                a.e(str_pre(X15, DSP, 8));
                a.next();
            }
            "car" | "cdr" => {
                a.e(ldr(X15, DSP, 0));
                a.check_tag(X15, TAG_PAIR, Trap::Type { routine: name });
                a.e(add(X14, BASE, X15));
                a.e(ldur(X15, X14, if name == "car" { -1 } else { 7 }));
                a.e(str(X15, DSP, 0));
                a.next();
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
                a.next();
                a.bind(slow);
                a.callout(n as u64);
            }
            "field!" | "cons" => a.callout(n as u64),
            // Not native yet (the routines for code compiled from FX-26):
            // a trap, as for a number that is no routine.
            _ => {
                a.e(movz(X13, Trap::NoRoutine(0).code().0 as u32, 0));
                a.e(movz(X14, n as u32, 0));
                let tc = a.trap_common;
                a.b(tc);
            }
        }
        a.flush_stubs();
    }
    (a.finish(), entry, starts)
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
    let heap = unsafe { &mut *(st.heap as *mut Heap) };
    let nds = (st.ds_base - st.dsp) as usize / 8;
    let nrs = (st.rs_base - st.rsp) as usize / 8;
    let ds = unsafe { std::slice::from_raw_parts_mut(st.dsp as *mut Value, nds) };
    let rs = unsafe { std::slice::from_raw_parts_mut(st.rsp as *mut Value, nrs) };
    let name = ROUTINES[n as usize].0;
    let result = callout_routine(heap, st, ds, rs, name);
    st.base = heap.active_words() as u64;
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
            let mut cur = [Value(st.cur)];
            heap.maybe_collect(&mut [ds, rs, &mut cur]);
            st.cur = cur[0].raw();
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
        Stacks { ds: Stack::new(8 * (DS_LIMIT + MAX_CELLS), 8 * MAX_CELLS), rs: Stack::new(16 * (RS_LIMIT + 2), page()) }
    }

    /// The state to start `word` in, with `args` on the data stack (the last
    /// on top). The heap must stay exclusively the machine's until the run
    /// ends.
    pub(crate) fn start(&mut self, heap: &mut Heap, word: Value, args: &[Value], fuel: u64) -> State {
        assert!(fixpt_engine::threaded::is_word(heap, word), "{word:?} is not a threaded word");
        assert_eq!(
            heap.bloblet_slot(word, WORD_ENTRY).as_fixnum() as u64,
            ROUTINE_DOCOL,
            "the machine starts with a word made of cells"
        );
        assert!(args.len() <= DS_LIMIT);
        let dsp = self.ds.base - 8 * args.len() as u64;
        for (i, a) in args.iter().rev().enumerate() {
            // SAFETY: inside the data stack's room, just below its base.
            unsafe { *((dsp + 8 * i as u64) as *mut u64) = a.raw() };
        }
        State {
            base: heap.active_words() as u64,
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
            rs_limit: self.rs.base - 16 * (RS_LIMIT as u64 + 1),
            routines: [0; ROUTINE_SLOTS],
        }
    }

    /// What a run that stopped in `st` produced: the data stack, bottom
    /// first, or its trap.
    pub(crate) fn finish(&self, st: &State) -> Result<Vec<Value>, Trap> {
        if st.status != 0 {
            return Err(Trap::from_code(st.status, st.aux));
        }
        let n = (self.ds.base - st.dsp) as usize / 8;
        // SAFETY: the machine's data stack, from its pointer to its base.
        let ds = unsafe { std::slice::from_raw_parts(st.dsp as *const Value, n) };
        Ok(ds.iter().rev().copied().collect())
    }
}

/// The native machine: its code, generated once, and its stacks.
pub struct NativeMachine {
    space: CodeSpace,
    entry: Offset,
    table: Vec<u64>,
    stacks: Stacks,
    /// Fuel left after the last run.
    pub fuel_left: u64,
}

impl NativeMachine {
    pub fn new() -> NativeMachine {
        let (code, entry, starts) = generate();
        let mut space = CodeSpace::new(code.len() * 4).expect("a code space");
        let at = space.alloc(code.len() * 4, 16).expect("room for the machine");
        space.write_code(at, &code);
        space.flush(at, code.len() * 4);
        let table = starts.iter().map(|s| space.exec_addr(at + 4 * s) as u64).collect();
        NativeMachine { entry: at + 4 * entry, space, table, stacks: Stacks::new(), fuel_left: 0 }
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
}

impl Default for NativeMachine {
    fn default() -> NativeMachine {
        NativeMachine::new()
    }
}
