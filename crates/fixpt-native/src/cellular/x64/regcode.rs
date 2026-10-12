//! Register code (PLAN.md 13h′) on x86_64: `cellular::regcode`'s
//! `assemble_register_word` and `assemble_adapter` for the other
//! instruction set, kept as close to them as the two allow, step for step.
//!
//! What x86_64 changes (CLAUDES_CHOICES.md, "Register code on x86_64"):
//! - Fewer registers. `RESULT` is `rax`; `REG1`…`REG3` are `rdi`, `rsi`
//!   and `r8`; `REG0` is `CLO`; `REG4`…`REG8` live in the state
//!   (`State::regs`). The front end's register code uses REG1 to REG3 for
//!   nine in ten of its operands (`fixpt regcode-survey`).
//! - No pool pointer: a 32-bit displacement from `CUR` reaches any of the
//!   word's fields, so `IP`'s register, `r14`, is scratch here, as are
//!   `rcx`, `rdx` and `r11`. `IP` is made only where something reads it as
//!   an ip (`save`, a return entry).
//! - No link register. A call is a `call`, which pushes where it returns
//!   to; `save` pops that into the frame's link slot, and `pop` pushes it
//!   back for `return`'s `ret`, or for the callee of a tail call. A leaf
//!   keeps it on the machine stack, and in the state (`leaf_link`) while it
//!   calls out. So the machine stack is never more than one link deep, and
//!   the machine's exit returns to where its entry left it (`machine_sp`).
//!   Return points are 8-aligned, so that a link in a frame reads as a
//!   fixnum, as on arm64.

use super::*;
use fixpt_heap::layout::cellular::{routine, GLOBAL_WRITES, WORD_NAME, WORD_TWIN};
use fixpt_heap::layout::regcode::{OPS, REGS};

const RESULT: Reg = RAX;
/// `IP`'s register, scratch while register code runs.
const T: Reg = R14;
/// The registers `REG0`…`REG3` live in.
const IN_REGS: [Reg; 4] = [CLO, RDI, RSI, R8];

/// Where `REGk` is: a register, or a word of the state.
#[derive(Copy, Clone)]
enum Loc {
    R(Reg),
    M(Mem),
}

fn loc(k: usize) -> Loc {
    match IN_REGS.get(k) {
        Some(&r) => Loc::R(r),
        None => Loc::M(st(offset_of!(State, regs) + 8 * k)),
    }
}

/// Field `f` of the running register word, from `CUR`.
fn cell_mem(f: usize) -> Mem {
    m(CUR, -((4 + 8 * f) as i32))
}

/// Whether runtime primitive `p` is the one called `name`.
fn prim_named(p: usize, name: &str) -> bool {
    fixpt_runtime::PRIMITIVES.get(p).is_some_and(|d| d.name == name)
}

impl Asm {
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
            Loc::R(r) => {
                if r != src {
                    self.e(mov(r, src));
                }
            }
            Loc::M(mem) => self.e(store(mem, src)),
        }
    }
    /// `REGk` := frame slot `n`, or the other way with `store`.
    fn slot_reg(&mut self, k: usize, n: usize, store_it: bool) {
        let slot = m(FP, -8 * n as i32);
        match (loc(k), store_it) {
            (Loc::R(r), false) => self.e(load(r, slot)),
            (Loc::R(r), true) => self.e(store(slot, r)),
            (Loc::M(mem), false) => {
                self.e(load(X16, slot));
                self.e(store(mem, X16));
            }
            (Loc::M(mem), true) => {
                self.e(load(X16, mem));
                self.e(store(slot, X16));
            }
        }
    }
    /// `dst` := field `f` of the running register word.
    fn cell(&mut self, dst: Reg, f: usize) {
        self.e(load(dst, cell_mem(f)));
    }
    /// `dst` := the operand `v`, field `f`: in the instruction if it is
    /// immediate, else from the word.
    fn constant(&mut self, dst: Reg, v: Value, f: usize) {
        if v.is_fixnum() || v.raw() & 7 == 3 {
            self.e(mov_imm(dst, v.raw()));
        } else {
            self.cell(dst, f);
        }
    }
    fn value(&mut self, dst: Reg, v: Value) {
        self.e(mov_imm(dst, v.raw()));
    }
    /// `IP` := the address of the running word's field `f`, as a cellular
    /// ip is, for what reads the word from where the ip is (`save`).
    fn ip_at(&mut self, f: usize) {
        self.e(lea(IP, cell_mem(f)));
    }
    /// No-ops so that an instruction of `len` bytes, placed next, ends
    /// 8-aligned: a `call`'s return point, which a frame keeps as a link
    /// that must read as a fixnum. Words start 32-aligned.
    fn align_return(&mut self, len: usize) {
        let pad = (self.here() + len).next_multiple_of(8) - (self.here() + len);
        self.code.extend_from_slice(&nops(pad));
        self.last_jump = None;
    }
    /// Push `REG1`…`REGn`, `REG1` deepest (uses `X16`, and `X13` and `X14`
    /// past `REGS`).
    fn push_regs(&mut self, n: usize) {
        if n <= REGS {
            for k in 1..=n {
                let r = self.get(k, X16);
                self.push_ds(r);
            }
            return;
        }
        // Past `REGS`, the rest are a list in the last register.
        for k in 1..REGS {
            let r = self.get(k, X16);
            self.push_ds(r);
        }
        let r = self.get(REGS, X14);
        if r != X14 {
            self.e(mov(X14, r));
        }
        for _ in REGS..=n {
            self.e(load(X13, m(X14, -1)));
            self.push_ds(X13);
            self.e(load(X14, m(X14, 7)));
        }
    }
    /// A call-out to routine `n` with the ip at field `f`: on, whatever
    /// the routine, to the code after it, or, for control, to the resume
    /// point `f` names.
    fn r_callout(&mut self, n: u64, f: usize) {
        self.ip_at(f);
        self.save();
        self.e(mov(RDI, ST));
        self.e(mov_imm(RSI, n));
        self.e(call_m(st(offset_of!(State, callout))));
        self.e(test(RAX, RAX));
        let exit = self.exit_common;
        self.jcc(Cond::Ne, exit);
        self.load();
        if super::super::CONTROL_CALLOUTS.contains(&ROUTINES[n as usize].0) {
            self.enter_cur(X13);
        }
    }

    /// `RESULT` := primitive `p` (one that never collects) of `RESULT` and
    /// `y`, called in Rust (`pure_call`) with no safepoint; its failure a
    /// trap. `REG0`…`REG3` and `TABLE`, which Rust may change, are kept on
    /// the machine stack around it, and the stack 16-aligned for it.
    fn pure_call(&mut self, p: usize, y: Reg) {
        self.pure_call3(p, y, None);
    }
    /// The same of `RESULT`, `y` and `z` (`prim3imm`). `y` and `z` are not
    /// `RDX` or `RCX`, nor `z` `X16`.
    fn pure_call3(&mut self, p: usize, y: Reg, z: Option<Reg>) {
        if y != X16 {
            self.e(mov(X16, y));
        }
        if let Some(z) = z
            && z != T
        {
            self.e(mov(T, z));
        }
        let saved = [RDI, RSI, R8, CLO, TABLE];
        for r in saved {
            self.e(push(r));
        }
        // With the link in the frame, the stack is as the machine's entry
        // left it, 16-aligned, and five pushes take it off by 8.
        if !self.link_pushed {
            self.e(sub_imm(RSP_, 8));
        }
        self.e(mov(RDX, RESULT));
        self.e(mov(RCX, X16));
        if z.is_some() {
            self.e(mov(R8, T));
        }
        self.e(mov(RDI, ST));
        self.e(mov_imm(RSI, p as u64));
        self.e(call_m(st(offset_of!(State, pure))));
        if !self.link_pushed {
            self.e(add_imm(RSP_, 8));
        }
        for r in saved.iter().rev() {
            self.e(pop(*r));
        }
        // `PureOut`: the value in `rax`, whether it failed in `rdx`.
        self.e(test(RDX, RDX));
        self.trap_if(Cond::Ne, Trap::Prim(String::new()));
    }

    /// `modulo`, `quotient`, `*` and `arithmetic-shift` of the fixnums in
    /// `RESULT` and `y`, into `RESULT`, as `regcode`'s `int_fast` does
    /// them: whether this is one, its fast path emitted, to `slow` (the
    /// call) for what it leaves, with `RESULT` and `y` as they were. `y`
    /// is not `RCX`, `RDX` or `X16`.
    fn int_fast(&mut self, name: &str, y: Reg, slow: Label) -> bool {
        if !matches!(name, "modulo" | "%fx26-quotient" | "%fx26-mul" | "%fx26-arithmetic-shift") {
            return false;
        }
        let x = RESULT;
        self.e(mov(RCX, x));
        self.e(or(RCX, y));
        self.e(test_imm(RCX, 7));
        self.jcc(Cond::Ne, slow);
        match name {
            // A product in 61 bits: the 64-bit product did not overflow.
            "%fx26-mul" => {
                self.e(mov(RDX, y));
                self.e(sar_imm(RDX, 3));
                self.e(mov(RCX, x));
                self.e(imul(RCX, RDX));
                self.jcc(Cond::O, slow);
                self.e(mov(RESULT, RCX));
            }
            // The quotient of the two raw values is the quotient's value,
            // the remainder the remainder's raw value. A quotient past a
            // fixnum is the primitive's; a remainder is `modulo`'s when it
            // has the divisor's sign, or is 0. `idiv` takes `RESULT`, kept
            // in `X16` for the slow path.
            "%fx26-quotient" | "modulo" => {
                self.e(test(y, y));
                self.jcc(Cond::E, slow);
                self.e(mov(X16, x));
                self.e(cqo());
                self.e(idiv(y));
                if name == "%fx26-quotient" {
                    let (ok, restore) = (self.label(), self.label());
                    self.e(mov(RCX, RAX));
                    self.e(shl_imm(RCX, 3));
                    self.e(sar_imm(RCX, 3));
                    self.e(cmp(RCX, RAX));
                    self.jcc(Cond::Ne, restore);
                    self.e(shl_imm(RAX, 3));
                    self.jmp(ok);
                    self.bind(restore);
                    self.e(mov(RESULT, X16));
                    self.jmp(slow);
                    self.bind(ok);
                } else {
                    let signed = self.label();
                    self.e(test(RDX, RDX));
                    self.jcc(Cond::E, signed);
                    self.e(mov(RCX, RDX));
                    self.e(xor(RCX, y));
                    self.jcc(Cond::Ns, signed);
                    self.e(add(RDX, y));
                    self.bind(signed);
                    self.e(mov(RESULT, RDX));
                }
            }
            // Left while the result stays a fixnum; right (floor) by fewer
            // than 63.
            _ => {
                let (right, done) = (self.label(), self.label());
                self.e(mov(RCX, y));
                self.e(sar_imm(RCX, 3));
                self.e(test(RCX, RCX));
                self.jcc(Cond::L, right);
                self.e(cmp_imm(RCX, 61));
                self.jcc(Cond::Ge, slow);
                self.e(mov(RDX, x));
                self.e(shift_cl(Shift::Shl, RDX));
                self.e(mov(X16, RDX));
                self.e(shift_cl(Shift::Sar, X16));
                self.e(cmp(X16, x));
                self.jcc(Cond::Ne, slow);
                self.e(mov(RESULT, RDX));
                self.jmp(done);
                self.bind(right);
                self.e(neg(RCX));
                self.e(cmp_imm(RCX, 63));
                self.jcc(Cond::Ae, slow);
                self.e(mov(RDX, x));
                self.e(shift_cl(Shift::Sar, RDX));
                self.e(sar_imm(RDX, 3));
                self.e(shl_imm(RDX, 3));
                self.e(mov(RESULT, RDX));
                self.bind(done);
            }
        }
        true
    }

    /// Shape predicate `name` of `src` into `RESULT` (`TODO.md` §56), as
    /// `regcode`'s `shape_test`: by the value's tag, and for a bloblet by
    /// its header's kind; to `slow` for anything else. False if `name` is
    /// none. Uses `RCX`, `RDX` and `X16`.
    fn shape_test(&mut self, src: Reg, name: &str, slow: Label) -> bool {
        use fixpt_heap::value::TAG_HEADER;
        let codes: Vec<i32> = match name {
            "pair?" | "char?" | "%fx26-f32?" | "null?" => {
                if name == "pair?" {
                    self.e(mov(RCX, src));
                    self.e(and_imm(RCX, 7));
                    self.e(cmp_imm(RCX, TAG_PAIR as i32));
                } else if name == "null?" {
                    self.cmp_value(src, Value::NULL);
                } else {
                    let tag = if name == "char?" { Value::char('\0') } else { Value::f32(0.0) };
                    self.e(movzx8(RCX, src));
                    self.e(cmp_imm(RCX, (tag.raw() & 0xFF) as i32));
                }
                self.boolean(RESULT, Cond::E);
                return true;
            }
            "boolean?" => {
                self.e(load(RCX, st(offset_of!(State, fal))));
                self.cmp_value(src, Value::FALSE);
                self.e(cmov_m(Cond::E, RCX, st(offset_of!(State, tru))));
                self.cmp_value(src, Value::TRUE);
                self.e(cmov_m(Cond::E, RCX, st(offset_of!(State, tru))));
                self.e(mov(RESULT, RCX));
                return true;
            }
            "symbol?" => vec![const { kind("symbol") }],
            "string?" => vec![const { kind("string") }],
            "exact-integer?" => vec![const { kind("bignum") }],
            "%fx26-array?" => vec![const { kind("bloblet") }],
            "%fx26-box?" => vec![const { kind("box") }],
            "%fx26-sum?" => vec![const { kind("sum") }],
            "%fx26-product?" => vec![const { kind("product") }],
            "%fx26-procedure?" => ["closure", "primitive", "continuation", "cellular-closure", "native-closure", "cellular-continuation"]
                .iter()
                .map(|n| kind(n))
                .collect(),
            _ => return false,
        }
        .into_iter()
        .map(i32::from)
        .collect();
        let (yes, no, have, end) = (self.label(), self.label(), self.label(), self.label());
        if name == "exact-integer?" {
            self.e(test_imm(src, 7));
            self.jcc(Cond::E, yes);
        }
        self.e(mov(RCX, src));
        self.e(and_imm(RCX, 7));
        self.e(cmp_imm(RCX, TAG_BLOBLET as i32));
        self.jcc(Cond::Ne, no);
        self.e(load(X16, field(src, 1)));
        self.e(mov(RCX, X16));
        self.e(and_imm(RCX, 7));
        self.e(cmp_imm(RCX, TAG_HEADER as i32));
        self.jcc(Cond::E, have);
        self.e(cmp_imm(RCX, TAG_TRAILER as i32));
        self.jcc(Cond::Ne, slow);
        self.e(sub_imm(X16, TAG_TRAILER as i32));
        self.e(mov(RDX, src));
        self.e(sub(RDX, X16));
        self.e(load(X16, field(RDX, 1)));
        self.bind(have);
        let k = fixpt_heap::layout::H_KIND;
        self.e(mov(RCX, X16));
        self.e(shr_imm(RCX, k.lo as u8));
        self.e(and_imm(RCX, ((1u64 << k.width) - 1) as i32));
        self.e(cmp_imm(RCX, fixpt_heap::layout::KIND_EXTENSION as i32));
        self.jcc(Cond::E, slow);
        for c in codes {
            self.e(cmp_imm(RCX, c));
            self.jcc(Cond::E, yes);
        }
        self.bind(no);
        self.value(RESULT, Value::FALSE);
        self.jmp(end);
        self.bind(yes);
        self.value(RESULT, Value::TRUE);
        self.bind(end);
        true
    }

    /// Room for `n` words: from the heap's free space, short of where a
    /// collection is due, or, with `region`, from the current chunk of the
    /// region whose handle is in `REG1` (`rcons`'s way). Its address in
    /// `RESULT`, the free space already bumped; to `slow` if there is none.
    /// Uses `RCX`, `RDX`, `X16` and `T`.
    fn bump_words(&mut self, n: u32, region: bool, slow: Label) {
        let r1 = IN_REGS[1];
        if region {
            self.e(test_imm(r1, 7));
            self.jcc(Cond::Ne, slow);
            self.e(cmp_imm(r1, 8 * fixpt_heap::heap::REGION_SLOTS as i32));
            self.jcc(Cond::Ae, slow);
            self.e(load(RCX, st(offset_of!(State, regions))));
            self.e(lea(RCX, mi(RCX, r1, 2, 0)));
            self.e(load(RDX, m(RCX, 0)));
            self.e(load(T, m(RCX, 8)));
        } else {
            self.e(load(RCX, st(offset_of!(State, top))));
            self.e(load(RDX, m(RCX, 0)));
            self.e(load(T, st(offset_of!(State, alloc_limit))));
        }
        self.e(lea(X16, m(RDX, n as i32)));
        self.e(cmp(X16, T));
        self.jcc(Cond::A, slow);
        self.e(load(T, st(offset_of!(State, words))));
        self.e(lea(RESULT, mi(T, RDX, 8, 0)));
        self.e(store(m(RCX, 0), X16));
    }

    /// A bloblet of `total` fields, the last its trailer, and no suffix, at
    /// `RESULT`, from `bump_words`: its header (in `T`) and its trailer.
    /// The other fields are the caller's to store (`field_at`), and then
    /// `bloblet_done` makes `RESULT` its pointer.
    fn bloblet_at(&mut self, total: usize) {
        self.e(store(m(RESULT, 0), T));
        self.e(mov_imm(T, fixpt_heap::layout::T_DISTANCE.put(TAG_TRAILER, total as u64)));
        self.e(store(m(RESULT, 8 * total as i32), T));
    }
    fn bloblet_done(&mut self, total: usize) {
        self.e(add_imm(RESULT, (8 * (1 + total) + TAG_BLOBLET as usize) as i32));
    }
    /// Store `r` as field `k` of the bloblet of `total` fields at `RESULT`.
    fn field_at(&mut self, r: Reg, k: usize, total: usize) {
        self.e(store(m(RESULT, 8 * (1 + total - k) as i32), r));
    }
    /// `REGj` as field `k` (uses `RCX`).
    fn reg_field_at(&mut self, j: usize, k: usize, total: usize) {
        let r = self.get(j, RCX);
        self.field_at(r, k, total);
    }

    /// `what` on `REG1`…`REGn` (`count` of them) into `RESULT`, without
    /// calling out; to `slow` when it cannot be done so. `word` is the
    /// field of a closure's word, for `closure`.
    fn inline_op(&mut self, what: &str, count: usize, word: usize, slow: Label) {
        use fixpt_heap::layout::cellular::{CLOSURE_FREE0, CLOSURE_WORD};
        use fixpt_heap::value::make_header;
        let (r1, r2, r3) = (IN_REGS[1], IN_REGS[2], IN_REGS[3]);
        match what {
            // A closure over `REG1`…`REGn`: the `closure` routine's object,
            // or `%region-closure`'s in the region in `REG1`, whose word is
            // the last operand.
            "closure" | "region-closure" => {
                let region = what == "region-closure";
                let frees: Vec<usize> = if region { (2..count).collect() } else { (1..=count).collect() };
                let total = frees.len() + 2;
                self.bump_words(1 + total as u32, region, slow);
                self.e(mov_imm(T, make_header(const { kind("cellular-closure") }, total, 0)));
                self.bloblet_at(total);
                if region {
                    self.reg_field_at(count, CLOSURE_WORD, total);
                } else {
                    self.cell(RCX, word);
                    self.field_at(RCX, CLOSURE_WORD, total);
                }
                for (i, j) in frees.iter().enumerate() {
                    self.reg_field_at(*j, CLOSURE_FREE0 + i, total);
                }
                self.bloblet_done(total);
            }
            // A sum or a product (`%make-frozen`): `REG1` its kind, a fixnum,
            // whose bits are the header's kind as they are; its fields frozen.
            "frozen" => {
                let total = count;
                self.bump_words(1 + total as u32, false, slow);
                let h = make_header(0, total, 0);
                let h = fixpt_heap::layout::H_FIELDS_FROZEN.put(h, 1);
                let h = fixpt_heap::layout::H_SUFFIX_FROZEN.put(h, 1);
                self.e(mov_imm(T, h));
                self.e(add(T, r1));
                self.bloblet_at(total);
                for j in 2..=count {
                    self.reg_field_at(j, j, total);
                }
                self.bloblet_done(total);
            }
            // A mutable bloblet of no suffix (`%make-bloblet`, `REG1` its
            // suffix's bytes, 0, else the call-out): its fields the rest of
            // the registers, as `frozen`'s are, but writable (`TODO.md` §57).
            "bloblet" => {
                let total = count;
                self.e(test(r1, r1));
                self.jcc(Cond::Ne, slow);
                self.bump_words(1 + total as u32, false, slow);
                self.e(mov_imm(T, make_header(const { kind("bloblet") }, total, 0)));
                self.bloblet_at(total);
                for j in 2..=count {
                    self.reg_field_at(j, j, total);
                }
                self.bloblet_done(total);
            }
            // `rnew`: a box in the region in `REG1`, holding `REG2`.
            "rnew" => {
                self.bump_words(3, true, slow);
                self.e(mov_imm(T, make_header(fixpt_heap::ObjType::Box as u8, 2, 0)));
                self.bloblet_at(2);
                self.field_at(r2, 2, 2);
                self.bloblet_done(2);
            }
            // `new` (`%make-box`): a box in the heap, holding `REG1`.
            "box" => {
                self.bump_words(3, false, slow);
                self.e(mov_imm(T, make_header(fixpt_heap::ObjType::Box as u8, 2, 0)));
                self.bloblet_at(2);
                self.field_at(r1, 2, 2);
                self.bloblet_done(2);
            }
            // `rmake-icell`: two fields, both `#f`, in the region in `REG1`.
            "ricell" => {
                self.bump_words(4, true, slow);
                self.e(mov_imm(T, make_header(const { kind("bloblet") }, 3, 0)));
                self.bloblet_at(3);
                self.value(RCX, Value::FALSE);
                self.field_at(RCX, 2, 3);
                self.field_at(RCX, 3, 3);
                self.bloblet_done(3);
            }
            // Field `REG2` (8k, a fixnum) of the bloblet in `REG1`, whose
            // trailer says how many it has: 2 ≤ k ≤ F, else the call-out
            // reports it.
            "field@" => {
                self.e(load(X16, field(r1, 1)));
                self.e(mov(RCX, X16));
                self.e(and_imm(RCX, 7));
                self.e(cmp_imm(RCX, TAG_TRAILER as i32));
                self.jcc(Cond::Ne, slow);
                self.e(cmp_imm(r2, 16));
                self.jcc(Cond::L, slow);
                self.e(sub_imm(X16, TAG_TRAILER as i32));
                self.e(cmp(r2, X16));
                self.jcc(Cond::G, slow);
                self.e(mov(RDX, r1));
                self.e(sub(RDX, r2));
                self.e(load(RESULT, m(RDX, -4)));
            }
            // How many fields the bloblet in `REG1` has, by its trailer.
            "fields" => {
                self.e(load(X16, field(r1, 1)));
                self.e(mov(RCX, X16));
                self.e(and_imm(RCX, 7));
                self.e(cmp_imm(RCX, TAG_TRAILER as i32));
                self.jcc(Cond::Ne, slow);
                self.e(mov(RESULT, X16));
                self.e(sub_imm(RESULT, TAG_TRAILER as i32));
            }
            // `%bloblet-set!`: `REG3` into field `REG2` (8k) of the bloblet in
            // `REG1`, 2 ≤ k ≤ F as `field@` checks; unspecified. Its fields
            // frozen (by an alias whose type does not say so), the call-out
            // refuses it.
            "field!" => {
                self.e(load(X16, field(r1, 1)));
                self.e(mov(RCX, X16));
                self.e(and_imm(RCX, 7));
                self.e(cmp_imm(RCX, TAG_TRAILER as i32));
                self.jcc(Cond::Ne, slow);
                self.e(cmp_imm(r2, 16));
                self.jcc(Cond::L, slow);
                self.e(sub_imm(X16, TAG_TRAILER as i32));
                self.e(cmp(r2, X16));
                self.jcc(Cond::G, slow);
                // The header: F + 1 words before the suffix.
                self.e(mov(RDX, r1));
                self.e(sub(RDX, X16));
                self.e(load(RCX, m(RDX, -12)));
                let frozen = fixpt_heap::layout::H_FIELDS_FROZEN;
                self.e(shr_imm(RCX, frozen.lo as u8));
                self.e(test_imm(RCX, 1));
                self.jcc(Cond::Ne, slow);
                self.e(mov(RDX, r1));
                self.e(sub(RDX, r2));
                self.e(store(m(RDX, -4), r3));
                self.es(&card_mark(RDX, -4, ST, offset_of!(State, cards) as i32, RCX, X16));
                self.value(RESULT, Value::UNSPECIFIED);
            }
            // `char-whitespace?` of an ASCII character: tab to carriage
            // return, or space. Past ASCII, Unicode's say, called out.
            "whitespace" => {
                self.e(mov(RCX, r1));
                self.e(sar_imm(RCX, 8));
                self.e(cmp_imm(RCX, 128));
                self.jcc(Cond::Ae, slow);
                self.e(lea(RDX, m(RCX, -9)));
                self.e(cmp_imm(RDX, 4));
                self.boolean(RESULT, Cond::Be);
                self.e(cmp_imm(RCX, 32));
                self.e(cmov_m(Cond::E, RESULT, st(offset_of!(State, tru))));
            }
            // `%symbol-hash`: the hash a symbol keeps, its field 1 of 3
            // (the checker has seen that it is a symbol).
            "symbol-hash" => {
                self.e(load(RESULT, field(r1, 3)));
            }
            "fixnum?" => {
                self.e(test_imm(r1, 7));
                self.boolean(RESULT, Cond::E);
            }
            // `int`'s bit operations of fixnums (`TODO.md` §56); a bignum
            // calls out.
            "bit-and" | "bit-ior" | "bit-xor" => {
                self.e(mov(RCX, r1));
                self.e(or(RCX, r2));
                self.e(test_imm(RCX, 7));
                self.jcc(Cond::Ne, slow);
                self.e(mov(RESULT, r1));
                self.e(match what {
                    "bit-and" => and(RESULT, r2),
                    "bit-ior" => or(RESULT, r2),
                    _ => xor(RESULT, r2),
                });
            }
            "bit-not" => {
                self.e(test_imm(r1, 7));
                self.jcc(Cond::Ne, slow);
                self.e(mov(RESULT, r1));
                self.e(neg(RESULT));
                self.e(sub_imm(RESULT, 8));
            }
            // Type tests: `shape_test`'s, of `REG1`.
            "char?" | "f32?" | "boolean?" | "pair?" | "symbol?" | "string?" | "exact-integer?" | "array?" | "box?" | "sum?" | "product?"
            | "procedure?" => {
                let name = match what {
                    "f32?" | "array?" | "box?" | "sum?" | "product?" | "procedure?" => format!("%fx26-{what}"),
                    _ => what.to_string(),
                };
                let done = self.shape_test(r1, &name, slow);
                debug_assert!(done);
            }
            // `char-numeric?` of an ASCII character: `0` to `9`. Past
            // ASCII, Unicode's say, called out.
            "numeric" => {
                self.e(mov(RCX, r1));
                self.e(sar_imm(RCX, 8));
                self.e(cmp_imm(RCX, 128));
                self.jcc(Cond::Ae, slow);
                self.e(lea(RDX, m(RCX, -('0' as i32))));
                self.e(cmp_imm(RDX, 9));
                self.boolean(RESULT, Cond::Be);
            }
            // `%fx26-char-in?`: whether the character in `REG1` is one of
            // the string in `REG2`'s, 32 bits each after its length.
            "char-in" => {
                let (again, yes, no, end) = (self.label(), self.label(), self.label(), self.label());
                self.e(mov(RCX, r1));
                self.e(sar_imm(RCX, 8));
                self.e(load(T, m(r2, -4)));
                self.e(mov(RDX, r2));
                self.bind(again);
                self.e(test(T, T));
                self.jcc(Cond::E, no);
                self.e(load32(X16, m(RDX, 4)));
                self.e(cmp(X16, RCX));
                self.jcc(Cond::E, yes);
                self.e(add_imm(RDX, 4));
                self.e(sub_imm(T, 1));
                self.jmp(again);
                self.bind(yes);
                self.value(RESULT, Value::TRUE);
                self.jmp(end);
                self.bind(no);
                self.value(RESULT, Value::FALSE);
                self.bind(end);
            }
            // `string=?` of two strings: their lengths, then their
            // characters, 32 bits each.
            "string=" => {
                let (again, yes, no, end) = (self.label(), self.label(), self.label(), self.label());
                self.e(load(T, m(r1, -4)));
                self.e(load(X16, m(r2, -4)));
                self.e(cmp(T, X16));
                self.jcc(Cond::Ne, no);
                self.e(mov(RCX, r1));
                self.e(mov(RDX, r2));
                self.bind(again);
                self.e(test(T, T));
                self.jcc(Cond::E, yes);
                self.e(load32(X16, m(RCX, 4)));
                self.e(load32(RESULT, m(RDX, 4)));
                self.e(cmp(X16, RESULT));
                self.jcc(Cond::Ne, no);
                self.e(add_imm(RCX, 4));
                self.e(add_imm(RDX, 4));
                self.e(sub_imm(T, 1));
                self.jmp(again);
                self.bind(yes);
                self.value(RESULT, Value::TRUE);
                self.jmp(end);
                self.bind(no);
                self.value(RESULT, Value::FALSE);
                self.bind(end);
            }
            // `modulo` of two fixnums: the remainder the divisor's sign, as
            // Scheme's `modulo` has it. Division by zero, and a bignum, are
            // the call-out's.
            "modulo" => {
                let end = self.label();
                self.e(mov(RCX, r1));
                self.e(or(RCX, r2));
                self.e(test_imm(RCX, 7));
                self.jcc(Cond::Ne, slow);
                self.e(test(r2, r2));
                self.jcc(Cond::E, slow);
                self.e(mov(RAX, r1));
                self.e(cqo());
                self.e(idiv(r2));
                self.e(mov(RESULT, RDX));
                self.e(test(RESULT, RESULT));
                self.jcc(Cond::E, end);
                self.e(mov(RCX, RESULT));
                self.e(xor(RCX, r2));
                self.jcc(Cond::Ns, end);
                self.e(add(RESULT, r2));
                self.bind(end);
            }
            // A pair from the heap's free space, if there is room short of
            // where a collection is due: `top` bumped by two words.
            "cons" => {
                self.e(load(RCX, st(offset_of!(State, top))));
                self.e(load(RDX, m(RCX, 0)));
                self.e(lea(X16, m(RDX, 2)));
                self.e(alu_rm(Alu::Cmp, X16, st(offset_of!(State, alloc_limit))));
                self.jcc(Cond::A, slow);
                self.e(load(RESULT, st(offset_of!(State, words))));
                self.e(lea(RESULT, mi(RESULT, RDX, 8, 0)));
                self.e(store(m(RESULT, 0), r1));
                self.e(store(m(RESULT, 8), r2));
                self.e(store(m(RCX, 0), X16));
                self.e(add_imm(RESULT, TAG_PAIR as i32));
            }
            // A string's length is its suffix's first word; its characters
            // follow, two to a word.
            "string-length" => {
                self.e(load(RESULT, m(r1, -4)));
                self.e(shl_imm(RESULT, 3));
            }
            "string-ref" => {
                self.e(load(X16, m(r1, -4)));
                self.e(mov(RCX, r2));
                self.e(sar_imm(RCX, 3));
                self.e(cmp(RCX, X16));
                self.jcc(Cond::Ae, slow);
                self.e(load32(RDX, mi(r1, RCX, 4, 4)));
                self.e(shl_imm(RDX, 8));
                self.value(RESULT, Value::char('\0'));
                self.e(add(RESULT, RDX));
            }
            // A pair in a region's current chunk, if the handle has a slot
            // in the heap's table and the chunk has room: its fill bumped
            // by two words. Anything else calls in.
            "rcons" => {
                self.e(test_imm(r1, 7));
                self.jcc(Cond::Ne, slow);
                self.e(cmp_imm(r1, 8 * fixpt_heap::heap::REGION_SLOTS as i32));
                self.jcc(Cond::Ae, slow);
                self.e(load(RCX, st(offset_of!(State, regions))));
                self.e(lea(RCX, mi(RCX, r1, 2, 0)));
                self.e(load(RDX, m(RCX, 0)));
                self.e(lea(X16, m(RDX, 2)));
                self.e(alu_rm(Alu::Cmp, X16, m(RCX, 8)));
                self.jcc(Cond::A, slow);
                self.e(load(RESULT, st(offset_of!(State, words))));
                self.e(lea(RESULT, mi(RESULT, RDX, 8, 0)));
                self.e(store(m(RESULT, 0), r2));
                self.e(store(m(RESULT, 8), r3));
                self.e(store(m(RCX, 0), X16));
                self.e(add_imm(RESULT, TAG_PAIR as i32));
            }
            other => unreachable!("{other} is not done inline"),
        }
    }

    fn es(&mut self, bytes: &[u8]) {
        self.code.extend_from_slice(bytes);
        self.last_jump = None;
    }
}

/// A register word's machine code, in bytes: its register entry first,
/// then an instruction's code after another; and where each cell's resume
/// point is (`-1` for none), for [`NativeMachine::install_bytes`].
pub fn assemble_register_word(heap: &Heap, rw: Value) -> Result<(Vec<u8>, Vec<i64>), String> {
    let fields = heap.bloblet_head(rw).fields;
    let cells: Vec<Value> = (WORD_CELL0..=fields).map(|k| heap.bloblet_slot(rw, k)).collect();
    let mut a = Asm::new();
    let labels: Vec<Label> = (0..=cells.len()).map(|_| a.label()).collect();
    let mut resume = vec![-1i64; cells.len()];
    // Whether the link is on the machine stack where each branch arrives,
    // as the branches say: `None` where none has yet.
    let mut pushed_at: Vec<Option<bool>> = vec![None; cells.len() + 1];
    // The register entry: called, the link on the machine stack.
    let entry = a.label();
    a.bind(entry);
    a.link_pushed = true;
    a.fuel();
    a.rs_limit();
    // Where a backward branch goes: a loop's head, 16-aligned, so that the
    // loop's speed does not depend on where the word lands.
    let mut loop_heads = vec![false; cells.len() + 1];
    let mut j = 0;
    while j < cells.len() {
        let (name, n, _) = OPS[cells[j].as_fixnum() as usize];
        if matches!(name, "branch" | "branchf" | "brancht" | "global-guard") {
            let to = j as i64 + 1 + n as i64 + cells[j + n].as_fixnum();
            if to <= j as i64 {
                loop_heads[to as usize] = true;
            }
        }
        j += 1 + n;
    }
    // Whether the code before falls through to here.
    let mut falls = true;
    let mut i = 0;
    while i < cells.len() {
        // Leaving (a return, a tail call), the code has no state to carry
        // on with: a branch's says where the link is.
        match (falls, pushed_at[i]) {
            (true, Some(p)) if p != a.link_pushed => return Err(format!("cell {i}: the link is on the stack by one path, not by another")),
            (false, Some(p)) => a.link_pushed = p,
            (false, None) => a.link_pushed = a.link.is_none(),
            _ => {}
        }
        if loop_heads[i] {
            a.align(16);
        }
        a.bind(labels[i]);
        let (name, n, _) = OPS[cells[i].as_fixnum() as usize];
        let o = |j: usize| cells[i + 1 + j];
        let f = |j: usize| WORD_CELL0 + i + 1 + j;
        let next = i + 1 + n;
        let k = |v: Value| v.as_fixnum() as usize;
        falls = true;
        let mut branch_to = |to: usize, pushed: bool| -> Result<(), String> {
            match pushed_at[to] {
                Some(p) if p != pushed => Err(format!("cell {i}: a branch to {to} disagrees on where the link is")),
                _ => {
                    pushed_at[to] = Some(pushed);
                    Ok(())
                }
            }
        };
        match name {
            "args" => {}
            "const" => a.constant(RESULT, o(0), f(0)),
            "global" | "setglbl" => {
                a.cell(X16, f(0));
                if name == "global" {
                    a.e(load(RESULT, field(X16, 2)));
                } else {
                    a.e(store(field(X16, 2), RESULT));
                    // One more write, for the guards (`global-guard`).
                    a.e(alu_mi(Alu::Add, field(X16, GLOBAL_WRITES), Value::fixnum(1).raw() as i32));
                    a.es(&card_mark(X16, -(4 + 8 * 2), ST, offset_of!(State, cards) as i32, RCX, RDX));
                }
            }
            "reg" => {
                let r = a.get(k(o(0)), RESULT);
                if r != RESULT {
                    a.e(mov(RESULT, r));
                }
            }
            "setreg" => a.put(k(o(0)), RESULT),
            "movereg" => {
                let r = a.get(k(o(0)), X16);
                a.put(k(o(1)), r);
            }
            "lexical" => {
                use fixpt_heap::layout::cellular::CLOSURE_FREE0;
                a.e(load(RESULT, field(CLO, CLOSURE_FREE0 + k(o(0)))));
            }
            // A frame of `m` slots, and below them the link, popped from
            // the machine stack, where the `call` (or the adapter) left it.
            // The collector scans the frame, and the link reads as a
            // fixnum: every return point is 8-aligned, and a call no `call`
            // made has 0 (the adapter).
            "save" => {
                let m_ = k(o(0));
                if !a.link_pushed {
                    return Err(format!("cell {i}: `save` with the link in a frame"));
                }
                a.link = Some(m_);
                a.e(sub_imm(DSP, 8 * (m_ as i32 + 1)));
                a.e(load(RCX, st(offset_of!(State, fal))));
                for s in 1..=m_ {
                    a.e(store(m(DSP, 8 * s as i32), RCX));
                }
                a.e(pop_m(m(DSP, 0)));
                a.link_pushed = false;
                a.e(lea(FP, m(DSP, 8 * m_ as i32)));
                a.ds_limit();
            }
            // The frame popped, its link pushed again for `return`, or for
            // a tail call's callee.
            "pop" => {
                let m_ = k(o(0));
                if a.link_pushed {
                    return Err(format!("cell {i}: `pop` with the link on the stack"));
                }
                a.e(push_m(m(DSP, 0)));
                a.link_pushed = true;
                a.e(add_imm(DSP, 8 * (m_ as i32 + 1)));
            }
            "stack" => a.e(load(RESULT, m(FP, -8 * k(o(0)) as i32))),
            "setstk" => a.e(store(m(FP, -8 * k(o(0)) as i32), RESULT)),
            "load" => a.slot_reg(k(o(0)), k(o(1)), false),
            "store" => a.slot_reg(k(o(0)), k(o(1)), true),
            "op1" => match ROUTINES[k(o(0))].0 {
                r @ ("pair-car" | "pair-cdr") => {
                    // A list may be `nil`: `car` of it traps.
                    a.e(mov(RCX, RESULT));
                    a.e(and_imm(RCX, 7));
                    a.e(cmp_imm(RCX, TAG_PAIR as i32));
                    a.trap_if(Cond::Ne, Trap::Type { routine: if r == "pair-car" { "pair-car" } else { "pair-cdr" } });
                    a.e(load(RESULT, m(RESULT, if r == "pair-car" { -1 } else { 7 })));
                }
                r => return Err(format!("op1 {r} in register code")),
            },
            "op2" | "op2imm" => {
                let other = if name == "op2" {
                    a.get(k(o(1)), T)
                } else {
                    a.constant(T, o(1), f(1));
                    T
                };
                // Ints: fixnums here; a bignum, or a sum past a fixnum, the
                // runtime's, called with no safepoint (PLAN.md, Q2).
                let r = ROUTINES[k(o(0))].0;
                let slow_prim = match r {
                    "int-add" => Some("%fx26-add"),
                    "int-sub" => Some("%fx26-sub"),
                    "int-less" => Some("%fx26-int-less"),
                    "int-eq" => Some("%fx26-int-eq"),
                    _ => None,
                };
                let (slow, done) = (a.label(), a.label());
                if slow_prim.is_some() {
                    a.e(mov(RCX, RESULT));
                    a.e(or(RCX, other));
                    a.e(test_imm(RCX, 7));
                    a.jcc(Cond::Ne, slow);
                }
                match r {
                    "int-add" | "int-sub" => {
                        a.e(mov(RCX, RESULT));
                        a.e(if r == "int-add" { add(RCX, other) } else { sub(RCX, other) });
                        a.jcc(Cond::O, slow);
                        a.e(mov(RESULT, RCX));
                    }
                    "int-less" | "eq" | "int-eq" => {
                        a.e(cmp(RESULT, other));
                        a.boolean(RESULT, if r == "int-less" { Cond::L } else { Cond::E });
                    }
                    r => return Err(format!("{name} {r} in register code")),
                }
                if let Some(pn) = slow_prim {
                    a.jmp(done);
                    a.bind(slow);
                    let p = fixpt_runtime::PRIMITIVES.iter().position(|d| d.name == pn).expect("a primitive");
                    a.pure_call(p, other);
                    a.bind(done);
                }
            }
            // A primitive that never collects: called with no safepoint.
            "prim1" | "prim2" | "prim2imm" => {
                let p = k(o(0));
                if !fixpt_runtime::PRIMITIVES.get(p).is_some_and(|d| fixpt_runtime::never_collects(d.name)) {
                    return Err(format!("`{name}` of primitive {p}, which may collect"));
                }
                let y = match name {
                    "prim2" => a.get(k(o(1)), T),
                    "prim2imm" => {
                        a.constant(T, o(1), f(1));
                        T
                    }
                    _ => T,
                };
                // A shape predicate in line (`TODO.md` §56), and fixnum
                // arithmetic; the call for what they leave.
                let (slow, done) = (a.label(), a.label());
                let pname = fixpt_runtime::PRIMITIVES[p].name;
                if (name == "prim1" && a.shape_test(RESULT, pname, slow)) || (name != "prim1" && a.int_fast(pname, y, slow)) {
                    a.jmp(done);
                    a.bind(slow);
                    a.pure_call(p, y);
                    a.bind(done);
                } else {
                    a.pure_call(p, y);
                }
            }
            // Of three: `RESULT`, a constant, `REGk`.
            "prim3imm" => {
                let p = k(o(0));
                if !fixpt_runtime::PRIMITIVES.get(p).is_some_and(|d| fixpt_runtime::never_collects(d.name)) {
                    return Err(format!("`{name}` of primitive {p}, which may collect"));
                }
                a.constant(X16, o(1), f(1));
                let z = a.get(k(o(2)), T);
                a.pure_call3(p, X16, Some(z));
            }
            "field" => a.e(load(RESULT, field(RESULT, k(o(0))))),
            "setfield" => {
                let v = a.get(k(o(1)), T);
                let mem = field(RESULT, k(o(0)));
                a.e(store(mem, v));
                a.es(&card_mark(RESULT, mem.disp, ST, offset_of!(State, cards) as i32, RCX, RDX));
            }
            "prim" | "lambda" | "cellular" => {
                let (count, routine_n, at) = match name {
                    "prim" => (k(o(1)), const { routine("prim") }, f(0)),
                    "lambda" => (k(o(1)), const { routine("closure") }, f(0)),
                    _ => (k(o(1)), k(o(0)) as u64, WORD_CELL0 + next),
                };
                // Some are done here, when they can be: the call-out is then
                // only the way for what cannot.
                let slow = a.label();
                let done = a.label();
                let inline = match (name, count) {
                    ("cellular", 2) if ROUTINES[k(o(0))].0 == "cons" => Some("cons"),
                    ("cellular", 2) if ROUTINES[k(o(0))].0 == "field@" => Some("field@"),
                    ("prim", 1) if prim_named(k(o(0)), "string-length") => Some("string-length"),
                    ("prim", 2) if prim_named(k(o(0)), "string-ref") => Some("string-ref"),
                    ("prim", 3) if prim_named(k(o(0)), "%region-cons") => Some("rcons"),
                    ("prim", 1) if prim_named(k(o(0)), "%bloblet-fields") => Some("fields"),
                    ("prim", 3) if prim_named(k(o(0)), "%bloblet-set!") => Some("field!"),
                    ("prim", 1) if prim_named(k(o(0)), "char-whitespace?") => Some("whitespace"),
                    ("prim", 1) if prim_named(k(o(0)), "char-numeric?") => Some("numeric"),
                    ("prim", 1) if prim_named(k(o(0)), "%symbol-hash") => Some("symbol-hash"),
                    ("prim", 1) if prim_named(k(o(0)), "%fx26-fixnum?") => Some("fixnum?"),
                    ("prim", 1) if prim_named(k(o(0)), "char?") => Some("char?"),
                    ("prim", 1) if prim_named(k(o(0)), "boolean?") => Some("boolean?"),
                    ("prim", 1) if prim_named(k(o(0)), "symbol?") => Some("symbol?"),
                    ("prim", 1) if prim_named(k(o(0)), "string?") => Some("string?"),
                    ("prim", 1) if prim_named(k(o(0)), "pair?") => Some("pair?"),
                    ("prim", 2) if prim_named(k(o(0)), "%fx26-bitwise-and") => Some("bit-and"),
                    ("prim", 2) if prim_named(k(o(0)), "%fx26-bitwise-ior") => Some("bit-ior"),
                    ("prim", 2) if prim_named(k(o(0)), "%fx26-bitwise-xor") => Some("bit-xor"),
                    ("prim", 1) if prim_named(k(o(0)), "%fx26-bitwise-not") => Some("bit-not"),
                    ("prim", 1) if prim_named(k(o(0)), "exact-integer?") => Some("exact-integer?"),
                    ("prim", 1) if prim_named(k(o(0)), "%fx26-array?") => Some("array?"),
                    ("prim", 1) if prim_named(k(o(0)), "%fx26-f32?") => Some("f32?"),
                    ("prim", 1) if prim_named(k(o(0)), "%fx26-box?") => Some("box?"),
                    ("prim", 1) if prim_named(k(o(0)), "%fx26-sum?") => Some("sum?"),
                    ("prim", 1) if prim_named(k(o(0)), "%fx26-product?") => Some("product?"),
                    ("prim", 1) if prim_named(k(o(0)), "%fx26-procedure?") => Some("procedure?"),
                    ("prim", 2) if prim_named(k(o(0)), "%fx26-char-in?") => Some("char-in"),
                    ("prim", 2) if prim_named(k(o(0)), "string=?") => Some("string="),
                    ("prim", 2) if prim_named(k(o(0)), "modulo") => Some("modulo"),
                    ("prim", 1) if prim_named(k(o(0)), "%make-box") => Some("box"),
                    ("prim", 2) if prim_named(k(o(0)), "%region-new") => Some("rnew"),
                    ("prim", 1) if prim_named(k(o(0)), "%region-make-icell") => Some("ricell"),
                    ("prim", c) if c >= 2 && c <= REGS && prim_named(k(o(0)), "%region-closure") => Some("region-closure"),
                    ("prim", c) if c >= 1 && prim_named(k(o(0)), "%make-frozen") => Some("frozen"),
                    ("prim", c) if c >= 1 && prim_named(k(o(0)), "%make-bloblet") => Some("bloblet"),
                    ("lambda", _) => Some("closure"),
                    _ => None,
                };
                if let Some(what) = inline.filter(|_| count <= REGS) {
                    a.inline_op(what, count, f(0), slow);
                    a.jmp(done);
                }
                a.bind(slow);
                // A leaf's link, kept in the state while it calls out, so
                // that the machine stack is as the machine's entry left it.
                let leaf = a.link_pushed;
                if leaf {
                    a.e(pop_m(st(offset_of!(State, leaf_link))));
                }
                a.push_regs(count);
                a.r_callout(routine_n, at);
                resume[next] = a.here() as i64;
                // Back from somewhere that may have collected: the value on
                // the data stack into `RESULT`.
                a.pop_ds(RESULT);
                if leaf {
                    a.e(push_m(st(offset_of!(State, leaf_link))));
                }
                a.bind(done);
            }
            "invoke" | "tailinvoke" => {
                let tail = name == "tailinvoke";
                let count = k(o(0));
                if tail != a.link_pushed {
                    return Err(format!("cell {i}: `{name}` with the link {}", if tail { "in a frame" } else { "on the stack" }));
                }
                let cellular = a.label();
                // Register code: the arguments stay where they are. A call
                // pushes a return entry marked as one `call` made (its `8k`
                // negated), so that the callee returns by `ret`, with the
                // value in `RESULT`; stack code has it made plain.
                if !tail {
                    a.ip_at(WORD_CELL0 + next);
                    a.push_return_marked();
                }
                // The callee, its word (in `T`), and the word's twin.
                a.e(load(T, field(RESULT, CLOSURE_WORD)));
                a.e(load(RDX, field(T, WORD_TWIN)));
                a.cmp_value(RDX, Value::FALSE);
                a.jcc(Cond::E, cellular);
                a.e(load(X16, field(RDX, WORD_ENTRY)));
                a.e(test(X16, X16));
                a.jcc(Cond::E, cellular);
                a.e(mov(CLO, RESULT));
                a.e(mov(CUR, RDX));
                let back = a.label();
                let target = mi(TABLE, X16, 1, 0);
                if tail {
                    a.e(jmp_m(target));
                } else {
                    let call = call_m(target);
                    a.align_return(call.len());
                    a.e(call);
                    a.jmp(back);
                }
                // Stack code: the arguments as its frame. It returns the
                // stack's way.
                a.bind(cellular);
                if !tail {
                    a.e(neg_m(m(RSP, 8)));
                }
                a.fuel();
                a.push_regs(count);
                a.ds_limit();
                a.rs_limit();
                if tail {
                    a.unmark_return();
                    // The link this procedure was called with, no use to
                    // stack code.
                    a.e(add_imm(RSP_, 8));
                }
                if count == 0 {
                    a.e(lea(FP, m(DSP, -8)));
                } else {
                    a.e(lea(FP, m(DSP, 8 * (count as i32 - 1))));
                }
                a.e(mov(CLO, RESULT));
                a.e(mov(CUR, T));
                a.ip_at(WORD_CELL0);
                a.e(mov_imm(RCX, (8 * WORD_CELL0) as u64));
                a.enter_cur(RCX);
                if tail {
                    falls = false;
                } else {
                    // Returned to the stack's way (the resume table), the
                    // value on the data stack; or by `ret`, in `RESULT`.
                    resume[next] = a.here() as i64;
                    a.pop_ds(RESULT);
                    a.bind(back);
                }
            }
            // A call of the procedure itself: its closure is the one running
            // and its word this one, so a `call` of this word's own entry.
            "invokeself" => {
                if a.link_pushed {
                    return Err(format!("cell {i}: `invokeself` with the link on the stack"));
                }
                let back = a.label();
                a.ip_at(WORD_CELL0 + next);
                a.push_return_marked();
                a.align_return(5);
                let at = a.here();
                a.to(entry, call(0));
                debug_assert_eq!(a.here() - at, 5);
                a.jmp(back);
                resume[next] = a.here() as i64;
                a.pop_ds(RESULT);
                a.bind(back);
            }
            // To an entry a `call` pushed: the caller's registers from it,
            // and back by `ret`. To any other entry, the stack's way, the
            // link (the adapter's 0) dropped.
            "return" => {
                if !a.link_pushed {
                    return Err(format!("cell {i}: `return` with the link in a frame"));
                }
                let stack = a.label();
                a.e(alu_mi(Alu::Cmp, m(RSP, 8), 0));
                a.jcc(Cond::Ge, stack);
                a.e(load(CUR, m(RSP, 0)));
                a.e(load(RDX, m(RSP, 16)));
                a.e(load(CLO, m(RSP, 24)));
                a.e(add_imm(RSP, 32));
                a.fp_decode(RDX);
                a.e(ret());
                a.bind(stack);
                a.push_ds(RESULT);
                a.e(add_imm(RSP_, 8));
                a.pop_return_of(true);
                falls = false;
            }
            "branch" | "branchf" | "brancht" => {
                let to = (i as i64 + 2 + o(0).as_fixnum()) as usize;
                branch_to(to, a.link_pushed)?;
                if name != "branch" {
                    a.cmp_value(RESULT, Value::FALSE);
                    a.jcc(if name == "branchf" { Cond::E } else { Cond::Ne }, labels[to]);
                } else {
                    if to <= i {
                        a.fuel();
                    }
                    a.jmp(labels[to]);
                    falls = false;
                }
            }
            // How many times the global has been written, against how many
            // when this code was compiled.
            "global-guard" => {
                let to = (i as i64 + 4 + o(2).as_fixnum()) as usize;
                branch_to(to, a.link_pushed)?;
                a.cell(X16, f(0));
                a.e(load(RCX, field(X16, GLOBAL_WRITES)));
                a.e(mov_imm(X16, o(1).raw()));
                a.e(cmp(RCX, X16));
                a.jcc(Cond::Ne, labels[to]);
            }
            other => return Err(format!("`{other}` in register code")),
        }
        i = next;
    }
    a.bind(labels[cells.len()]);
    // Out of the way of the code that runs: the traps.
    a.flush_stubs();
    // The machine's common trap and exit, through the state, as a word's
    // (`assemble_word`): no branch leaves this code.
    let [tc, ec] = [a.trap_common, a.exit_common];
    a.bind(tc);
    a.e(jmp_m(st(offset_of!(State, trap))));
    a.bind(ec);
    a.e(jmp_m(st(offset_of!(State, exit))));
    Ok((a.finish(), resume))
}

/// With `FIXPT_REGCODE_DUMP=file`, each register word's machine code is
/// appended to `file`, for looking at: a line of its name and where it
/// starts in the code space, then its instructions, as the disassembler
/// reads them.
pub(crate) fn dump(heap: &Heap, rw: Value, at: usize, code: &[u8]) {
    let Ok(file) = std::env::var("FIXPT_REGCODE_DUMP") else { return };
    let name = heap.symbol_name(heap.bloblet_slot(rw, WORD_NAME));
    let text = format!("// {name} at {at:#x}\n{}", crate::x86_64::disasm::listing(code));
    use std::io::Write;
    if let Ok(mut f) = std::fs::OpenOptions::new().create(true).append(true).open(file) {
        let _ = f.write_all(text.as_bytes());
    }
}

/// The entry a stack-code caller takes into a word with register code: the
/// `n` arguments from its frame into registers, the frame dropped, and on
/// to the register word's entry, native slot `slot`, with a link of 0 on
/// the machine stack, as no `call` made.
pub fn assemble_adapter(n: usize, slot: usize) -> Vec<u8> {
    let mut a = Asm::new();
    for i in 0..n {
        let slot_mem = m(FP, -8 * i as i32);
        match loc(i + 1) {
            Loc::R(r) => a.e(load(r, slot_mem)),
            Loc::M(mem) => {
                a.e(load(X16, slot_mem));
                a.e(store(mem, X16));
            }
        }
    }
    a.e(lea(DSP, m(FP, 8)));
    a.e(load(CUR, field(CUR, WORD_TWIN)));
    a.e(mov_imm(X16, 0));
    a.e(push(X16));
    a.e(jmp_m(m(TABLE, 8 * slot as i32)));
    a.finish()
}
