//! Register code (PLAN.md 13h′) as machine code, on the machine stack code
//! (cellular words, interpreted or compiled) runs on, so that each may call
//! the other. The two differ in their machine model, not in being compiled:
//! stack code passes and keeps every value on the data stack, register code
//! in registers.
//!
//! `RESULT` is `x0`; `REG1`…`REG8` are `x1`…`x8`; `REG0` is `CLO`. While
//! register code runs, `CUR` is its register word, and `IP`, which it has no
//! use for as an ip, points at the word's last field, so that its constants
//! and global cells are one load away (`cell`). Whatever may collect is a
//! call-out, or a call, and everything live is in the frame by then (the
//! compiler sees to it): afterwards the machine's registers are loaded from
//! the state, `IP` made again, and `RESULT` taken from the data stack, where
//! a call-out, or a return, leaves a value. Those resume points are what the
//! word's resume table lists, so that a return, or a continuation captured
//! in a call-out, comes back to them.
//!
//! A call whose callee's word has compiled register code jumps to it with
//! the arguments in registers; any other pushes them as a stack frame. A
//! stack-code caller enters a word with register code through the word's
//! own entry, which moves the frame's arguments into registers.

use super::*;
use fixpt_heap::layout::regcode::{OPS, REGS};
use fixpt_heap::layout::cellular::{routine, WORD_TWIN};

const RESULT: Reg = 0;
const X12: Reg = 12;

/// `REGk`'s machine register.
fn reg(k: usize) -> Reg {
    if k == 0 { CLO } else { k as Reg }
}

impl Asm {
    /// `RESULT` := primitive `p` (one that never collects) of `RESULT` and
    /// `y`, called in Rust (`pure_call`) with no safepoint, REG1…REG8 and
    /// the link kept on the machine stack around it; its failure a trap.
    fn pure_call(&mut self, p: usize, y: Reg) {
        self.e(mov(X14, y));
        for r in [1, 3, 5, 7] {
            self.e(stp_pre(r, r + 1, SP, -16));
        }
        self.e(stp_pre(LR, 31, SP, -16));
        self.e(mov(3, X14));
        self.e(mov(2, RESULT));
        self.e(mov(0, ST));
        self.es(&mov_imm64(1, p as u64));
        self.e(ldr(X16, ST, off(offset_of!(State, pure))));
        self.e(blr(X16));
        self.e(mov(X13, 1));
        self.e(ldp_post(LR, 31, SP, 16));
        for r in [7, 5, 3, 1] {
            self.e(ldp_post(r, r + 1, SP, 16));
        }
        self.e(cmp_imm(X13, 0));
        self.trap_if(Cond::Ne, Trap::Prim(String::new()));
    }
    /// `IP` := the address of the running register word's field `fields`,
    /// its last, from which field `f` is `8 × (fields − f)` bytes up.
    fn pool(&mut self, fields: usize) {
        self.e(mov(IP, CUR));
        self.sub_const(IP, IP, 4 + 8 * fields as u64);
    }
    /// `d := n − k`, for a constant `k` of any size (clobbers `X16`).
    fn sub_const(&mut self, d: Reg, n: Reg, k: u64) {
        if k < 4096 {
            self.e(sub_imm(d, n, k as u32));
        } else {
            self.es(&mov_imm64(X16, k));
            self.e(sub(d, n, X16));
        }
    }
    /// `dst` := field `f` of the running register word.
    fn cell(&mut self, dst: Reg, f: usize, fields: usize) {
        let off = 8 * (fields - f) as u64;
        if off < 32768 {
            self.e(ldr(dst, IP, off as u32));
        } else {
            self.es(&mov_imm64(X16, off));
            self.e(add(X16, IP, X16));
            self.e(ldr(dst, X16, 0));
        }
    }
    /// `dst` := field `f` of the bloblet whose `suffix + 4` is in `b`.
    fn field_of(&mut self, dst: Reg, b: Reg, f: usize) {
        let off = field_off(f);
        if off >= -256 {
            self.e(ldur(dst, b, off));
        } else {
            self.sub_const(X16, b, -off as u64);
            self.e(ldr(dst, X16, 0));
        }
    }
    /// Frame slot `n`: `8n` bytes below `FP`.
    fn slot(&mut self, r: Reg, n: usize, store: bool) {
        let off = 8 * n as i64;
        if off <= 256 {
            self.e(if store { stur(r, FP, -off) } else { ldur(r, FP, -off) });
        } else {
            self.sub_const(X16, FP, off as u64);
            self.e(if store { str(r, X16, 0) } else { ldr(r, X16, 0) });
        }
    }
    /// `IP` := the address of the running word's field `f`, as a cellular
    /// ip is, for what reads the word from where the ip is (`save`).
    fn ip_at(&mut self, f: usize) {
        self.e(mov(IP, CUR));
        self.sub_const(IP, IP, 4 + 8 * f as u64);
    }
    /// Push `REG1`…`REGn`, `REG1` deepest.
    fn push_regs(&mut self, n: usize) {
        if n <= REGS {
            for k in 1..=n {
                self.e(str_pre(reg(k), DSP, -8));
            }
            return;
        }
        // Past `REGS`, the rest are a list in the last register.
        for k in 1..REGS {
            self.e(str_pre(reg(k), DSP, -8));
        }
        self.e(mov(X16, reg(REGS)));
        for _ in REGS..=n {
            self.e(ldur(X13, X16, -1));
            self.e(str_pre(X13, DSP, -8));
            self.e(ldur(X16, X16, 7));
        }
    }
    /// Back from somewhere that may have collected: the value on the data
    /// stack into `RESULT`, and `IP` made again.
    fn resumed(&mut self, fields: usize) {
        self.e(ldr_post(RESULT, DSP, 8));
        self.pool(fields);
        self.relink();
    }
    /// `x30` is the link again, from the frame: after a call or a call-out,
    /// which change it. So it is the link wherever the procedure is, and
    /// leaving the frame need not load it.
    fn relink(&mut self) {
        match self.link {
            Some(m) => self.slot(LR, m, false),
            // A leaf's, kept in the state around its call-out.
            None => self.e(ldr(LR, ST, off(offset_of!(State, leaf_link)))),
        }
    }
    /// A call-out to routine `n` with the ip at field `f`: as
    /// [`callout`](Asm::callout), but on, whatever the routine, to the code
    /// after it, or, for control, to the resume point `f` names.
    fn r_callout(&mut self, n: u64, f: usize) {
        self.ip_at(f);
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
        }
    }
}

/// Whether runtime primitive `p` is the one called `name`.
fn prim_named(p: usize, name: &str) -> bool {
    fixpt_runtime::PRIMITIVES.get(p).is_some_and(|d| d.name == name)
}

impl Asm {
    /// `what` on `REG1`… into `RESULT`, without calling out; to `slow` when
    /// it cannot be done so.
    /// Room for `n` words: from the heap's free space, short of where a
    /// collection is due, or, with `region`, from the current chunk of the
    /// region whose handle is in `REG1` (`rcons`'s way). Its address in
    /// `X11`, the free space already bumped; to `slow` if there is none.
    fn bump_words(&mut self, n: u32, region: bool, slow: Label) {
        if region {
            self.e(tst_low(1, 3));
            self.b_cond(Cond::Ne, slow);
            self.e(cmp_imm(1, 8 * fixpt_heap::heap::REGION_SLOTS as u32));
            self.b_cond(Cond::Hs, slow);
            self.e(ldr(X13, ST, off(offset_of!(State, regions))));
            self.e(add_lsl(X13, X13, 1, 1));
            self.e(ldp(X14, X15, X13, 0));
        } else {
            self.e(ldr(X13, ST, off(offset_of!(State, top))));
            self.e(ldr(X14, X13, 0));
            self.e(ldr(X15, ST, off(offset_of!(State, alloc_limit))));
        }
        self.e(add_imm(X16, X14, n));
        self.e(cmp(X16, X15));
        self.b_cond(Cond::Hi, slow);
        self.e(ldr(W, ST, off(offset_of!(State, words))));
        self.e(add_lsl(X11, W, X14, 3));
        self.e(str(X16, X13, 0));
    }

    /// A bloblet of `total` fields, the last its trailer, and no suffix, at
    /// `X11`, from `bump_words`: its header (in `X15`), its trailer, and
    /// `RESULT` its pointer. The other fields are the caller's to store,
    /// field `k` at `X11 + 8 (1 + total − k)`.
    fn bloblet_at(&mut self, total: usize) {
        self.e(str(X15, X11, 0));
        self.es(&mov_imm64(X15, fixpt_heap::layout::T_DISTANCE.put(TAG_TRAILER, total as u64)));
        self.e(str(X15, X11, 8 * total as u32));
        self.e(add_imm(RESULT, X11, (8 * (1 + total) + TAG_BLOBLET as usize) as u32));
    }
    /// Store `r` as field `k` of the bloblet of `total` fields at `X11`.
    fn field_at(&mut self, r: Reg, k: usize, total: usize) {
        self.e(str(r, X11, 8 * (1 + total - k) as u32));
    }

    /// `what` on `REG1`…`REGn` (`count` of them) into `RESULT`, without
    /// calling out; to `slow` when it cannot be done so. `word` is the
    /// pool field of a closure's word, for `closure`.
    fn inline_op(&mut self, what: &str, count: usize, word: usize, fields: usize, slow: Label) {
        use fixpt_heap::layout::cellular::{CLOSURE_FREE0, CLOSURE_WORD};
        use fixpt_heap::value::make_header;
        match what {
            // A closure over `REG1`…`REGn`: the `closure` routine's object,
            // or `%region-closure`'s in the region in `REG1`, whose word is
            // the last operand.
            "closure" | "region-closure" => {
                let region = what == "region-closure";
                let frees: Vec<Reg> = if region { (2..count).map(reg).collect() } else { (1..=count).map(reg).collect() };
                let total = frees.len() + 2;
                self.bump_words(1 + total as u32, region, slow);
                self.es(&mov_imm64(X15, make_header(fixpt_heap::layout::kind("cellular-closure"), total, 0)));
                self.bloblet_at(total);
                if region {
                    self.field_at(reg(count), CLOSURE_WORD, total);
                } else {
                    self.cell(X15, word, fields);
                    self.field_at(X15, CLOSURE_WORD, total);
                }
                for (i, r) in frees.iter().enumerate() {
                    self.field_at(*r, CLOSURE_FREE0 + i, total);
                }
            }
            // A sum or a product (`%make-frozen`): `REG1` its kind, a fixnum,
            // whose bits are the header's kind as they are; its fields frozen.
            "frozen" => {
                let total = count;
                self.bump_words(1 + total as u32, false, slow);
                let h = make_header(0, total, 0);
                let h = fixpt_heap::layout::H_FIELDS_FROZEN.put(h, 1);
                let h = fixpt_heap::layout::H_SUFFIX_FROZEN.put(h, 1);
                self.es(&mov_imm64(X15, h));
                self.e(add(X15, X15, 1));
                self.bloblet_at(total);
                for j in 2..=count {
                    self.field_at(reg(j), j, total);
                }
            }
            // `rnew`: a box in the region in `REG1`, holding `REG2`.
            "rnew" => {
                self.bump_words(3, true, slow);
                self.es(&mov_imm64(X15, make_header(fixpt_heap::ObjType::Box as u8, 2, 0)));
                self.bloblet_at(2);
                self.field_at(2, 2, 2);
            }
            // `new` (`%make-box`): a box in the heap, holding `REG1`.
            "box" => {
                self.bump_words(3, false, slow);
                self.es(&mov_imm64(X15, make_header(fixpt_heap::ObjType::Box as u8, 2, 0)));
                self.bloblet_at(2);
                self.field_at(1, 2, 2);
            }
            // `rmake-icell`: two fields, both `#f`, in the region in `REG1`.
            "ricell" => {
                self.bump_words(4, true, slow);
                self.es(&mov_imm64(X15, make_header(fixpt_heap::layout::kind("bloblet"), 3, 0)));
                self.bloblet_at(3);
                self.value(X15, Value::FALSE);
                self.field_at(X15, 2, 3);
                self.field_at(X15, 3, 3);
            }
            // Field `REG2` (8k, a fixnum) of the bloblet in `REG1`, whose
            // trailer says how many it has: 2 ≤ k ≤ F, else the call-out
            // reports it.
            "field@" => {
                self.e(ldur(X16, 1, field_off(1)));
                self.e(and_low(X13, X16, 3));
                self.e(cmp_imm(X13, TAG_TRAILER as u32));
                self.b_cond(Cond::Ne, slow);
                self.e(cmp_imm(2, 16));
                self.b_cond(Cond::Lt, slow);
                self.e(sub_imm(X16, X16, TAG_TRAILER as u32));
                self.e(cmp(2, X16));
                self.b_cond(Cond::Gt, slow);
                self.e(sub(X11, 1, 2));
                self.e(ldur(RESULT, X11, -4));
            }
            // How many fields the bloblet in `REG1` has, by its trailer.
            "fields" => {
                self.e(ldur(X16, 1, field_off(1)));
                self.e(and_low(X13, X16, 3));
                self.e(cmp_imm(X13, TAG_TRAILER as u32));
                self.b_cond(Cond::Ne, slow);
                self.e(sub_imm(RESULT, X16, TAG_TRAILER as u32));
            }
            // `%bloblet-set!`: `REG3` into field `REG2` (8k) of the bloblet in
            // `REG1`, 2 ≤ k ≤ F as `field@` checks; unspecified. Its fields
            // frozen (by an alias whose type does not say so), the call-out
            // refuses it.
            "field!" => {
                self.e(ldur(X16, 1, field_off(1)));
                self.e(and_low(X13, X16, 3));
                self.e(cmp_imm(X13, TAG_TRAILER as u32));
                self.b_cond(Cond::Ne, slow);
                self.e(cmp_imm(2, 16));
                self.b_cond(Cond::Lt, slow);
                self.e(sub_imm(X16, X16, TAG_TRAILER as u32));
                self.e(cmp(2, X16));
                self.b_cond(Cond::Gt, slow);
                // The header: F + 1 words before the suffix.
                self.e(sub(X11, 1, X16));
                self.e(ldur(X13, X11, -12));
                let frozen = fixpt_heap::layout::H_FIELDS_FROZEN;
                self.e(ubfx(X13, X13, frozen.lo, 1));
                self.cbnz(X13, slow);
                self.e(sub(X11, 1, 2));
                self.e(stur(3, X11, -4));
                self.es(&card_mark(X11, -4, ST, off(offset_of!(State, cards)), X13, X16));
                self.value(RESULT, Value::UNSPECIFIED);
            }
            // `char-whitespace?` of an ASCII character: tab to carriage
            // return, or space. Past ASCII, Unicode's say, called out.
            "whitespace" => {
                self.e(asr_imm(X13, 1, 8));
                self.e(cmp_imm(X13, 128));
                self.b_cond(Cond::Hs, slow);
                self.value(X15, Value::TRUE);
                self.value(X16, Value::FALSE);
                self.e(sub_imm(X14, X13, 9));
                self.e(cmp_imm(X14, 4));
                self.e(csel(RESULT, X15, X16, Cond::Ls));
                self.e(cmp_imm(X13, 32));
                self.e(csel(RESULT, X15, RESULT, Cond::Eq));
            }
            // `%symbol-hash`: the hash a symbol keeps, its field 1 of 3
            // (the checker has seen that it is a symbol).
            "symbol-hash" => {
                self.e(ldur(RESULT, 1, field_off(3)));
            }
            // Type tests of any value: the fixnum, character and boolean
            // ones by the value alone.
            "fixnum?" => {
                self.e(tst_low(1, 3));
                self.value(X15, Value::TRUE);
                self.value(X16, Value::FALSE);
                self.e(csel(RESULT, X15, X16, Cond::Eq));
            }
            "char?" => {
                self.e(and_low(X13, 1, 8));
                self.e(cmp_imm(X13, (Value::char('\0').raw() & 0xFF) as u32));
                self.value(X15, Value::TRUE);
                self.value(X16, Value::FALSE);
                self.e(csel(RESULT, X15, X16, Cond::Eq));
            }
            "boolean?" => {
                self.value(X15, Value::FALSE);
                self.value(X16, Value::TRUE);
                self.e(cmp(1, X15));
                self.e(csel(RESULT, X16, X15, Cond::Eq));
                self.e(cmp(1, X16));
                self.e(csel(RESULT, X16, RESULT, Cond::Eq));
            }
            // `symbol?` and `string?`: a bloblet whose header says so. The
            // header is the word before the suffix when there are no
            // fields, or as far back as the trailer there says. Anything
            // else (a large object's extension, no trailer) calls out.
            "symbol?" | "string?" => {
                let code = if what == "symbol?" { fixpt_heap::ObjType::Symbol } else { fixpt_heap::ObjType::String } as u32;
                let (no, have, end) = (self.label(), self.label(), self.label());
                self.e(and_low(X13, 1, 3));
                self.e(cmp_imm(X13, TAG_BLOBLET as u32));
                self.b_cond(Cond::Ne, no);
                self.e(ldur(X16, 1, field_off(1)));
                self.e(and_low(X13, X16, 3));
                self.e(cmp_imm(X13, fixpt_heap::value::TAG_HEADER as u32));
                self.b_cond(Cond::Eq, have);
                self.e(cmp_imm(X13, TAG_TRAILER as u32));
                self.b_cond(Cond::Ne, slow);
                self.e(sub_imm(X16, X16, TAG_TRAILER as u32));
                self.e(sub(X11, 1, X16));
                self.e(ldur(X16, X11, field_off(1)));
                self.bind(have);
                let k = fixpt_heap::layout::H_KIND;
                self.e(ubfx(X13, X16, k.lo, k.width));
                self.e(cmp_imm(X13, fixpt_heap::layout::KIND_EXTENSION as u32));
                self.b_cond(Cond::Eq, slow);
                self.e(cmp_imm(X13, code));
                self.value(X15, Value::TRUE);
                self.value(X16, Value::FALSE);
                self.e(csel(RESULT, X15, X16, Cond::Eq));
                self.b(end);
                self.bind(no);
                self.value(RESULT, Value::FALSE);
                self.bind(end);
            }
            // `char-numeric?` of an ASCII character: `0` to `9`. Past
            // ASCII, Unicode's say, called out.
            "numeric" => {
                self.e(asr_imm(X13, 1, 8));
                self.e(cmp_imm(X13, 128));
                self.b_cond(Cond::Hs, slow);
                self.value(X15, Value::TRUE);
                self.value(X16, Value::FALSE);
                self.e(sub_imm(X14, X13, '0' as u32));
                self.e(cmp_imm(X14, 9));
                self.e(csel(RESULT, X15, X16, Cond::Ls));
            }
            // `%fx26-char-in?`: whether the character in `REG1` is one of
            // the string in `REG2`'s, 32 bits each after its length.
            "char-in" => {
                let (again, yes, no, end) = (self.label(), self.label(), self.label(), self.label());
                self.e(asr_imm(X13, 1, 8));
                self.e(ldur(X15, 2, -4));
                self.e(mov(X14, 2));
                self.bind(again);
                self.cbz(X15, no);
                self.e(ldur_w(X10, X14, 4));
                self.e(cmp(X10, X13));
                self.b_cond(Cond::Eq, yes);
                self.e(add_imm(X14, X14, 4));
                self.e(sub_imm(X15, X15, 1));
                self.b(again);
                self.bind(yes);
                self.value(RESULT, Value::TRUE);
                self.b(end);
                self.bind(no);
                self.value(RESULT, Value::FALSE);
                self.bind(end);
            }
            // `string=?` of two strings: their lengths, then their
            // characters, 32 bits each.
            "string=" => {
                let (again, yes, no, end) = (self.label(), self.label(), self.label(), self.label());
                self.e(ldur(X15, 1, -4));
                self.e(ldur(X16, 2, -4));
                self.e(cmp(X15, X16));
                self.b_cond(Cond::Ne, no);
                self.e(mov(X13, 1));
                self.e(mov(X14, 2));
                self.bind(again);
                self.cbz(X15, yes);
                self.e(ldur_w(X10, X13, 4));
                self.e(ldur_w(X11, X14, 4));
                self.e(cmp(X10, X11));
                self.b_cond(Cond::Ne, no);
                self.e(add_imm(X13, X13, 4));
                self.e(add_imm(X14, X14, 4));
                self.e(sub_imm(X15, X15, 1));
                self.b(again);
                self.bind(yes);
                self.value(RESULT, Value::TRUE);
                self.b(end);
                self.bind(no);
                self.value(RESULT, Value::FALSE);
                self.bind(end);
            }
            // `modulo` of two fixnums, whose bits are their values times
            // 8: the quotient's sign rounded toward zero, the remainder the
            // divisor's sign, as Scheme's `modulo` has it. Division by zero
            // is the call-out's to report.
            // Fixnums only: a bignum (`u64->int` makes one) is the
            // primitive's.
            "modulo" => {
                let end = self.label();
                self.e(orr(X13, 1, 2));
                self.e(tst_low(X13, 3));
                self.b_cond(Cond::Ne, slow);
                self.cbz(2, slow);
                self.e(sdiv(X13, 1, 2));
                self.e(msub(RESULT, X13, 2, 1));
                self.cbz(RESULT, end);
                self.e(eor(X14, RESULT, 2));
                self.e(cmp_imm(X14, 0));
                self.b_cond(Cond::Ge, end);
                self.e(add(RESULT, RESULT, 2));
                self.bind(end);
            }
            _ => self.inline(what, slow),
        }
    }

    fn inline(&mut self, what: &str, slow: Label) {
        match what {
            // A pair from the heap's free space, if there is room short of
            // where a collection is due: `top` bumped by two words.
            "cons" => {
                self.e(ldr(W, ST, off(offset_of!(State, words))));
                self.e(ldr(X13, ST, off(offset_of!(State, top))));
                self.e(ldr(X14, X13, 0));
                self.e(ldr(X15, ST, off(offset_of!(State, alloc_limit))));
                self.e(add_imm(X16, X14, 2));
                self.e(cmp(X16, X15));
                self.b_cond(Cond::Hi, slow);
                // The pair's address, and, off the path from `top` to the
                // result, its tag added to the base first.
                self.e(add_lsl(X11, W, X14, 3));
                self.e(add_imm(W, W, TAG_PAIR as u32));
                self.e(stp(1, 2, X11, 0));
                self.e(str(X16, X13, 0));
                self.e(add_lsl(RESULT, W, X14, 3));
            }
            // A string's length is its suffix's first word; its characters
            // follow, two to a word.
            "string-length" => {
                self.e(mov(X11, 1));
                self.e(ldur(X15, X11, -4));
                self.e(add_lsl(RESULT, XZR, X15, 3));
            }
            "string-ref" => {
                self.e(mov(X11, 1));
                self.e(ldur(X15, X11, -4));
                self.e(asr_imm(X13, 2, 3));
                self.e(cmp(X13, X15));
                self.b_cond(Cond::Hs, slow);
                self.e(add_lsl(X14, X11, X13, 2));
                self.e(ldur_w(X15, X14, 4));
                self.value(X16, Value::char('\0'));
                self.e(add_lsl(RESULT, X16, X15, 8));
            }
            // A pair in a region's current chunk, if the handle has a slot
            // in the heap's table and the chunk has room: its fill bumped
            // by two words. Anything else calls in: `#f`, the heap's; a
            // region with no chunk yet, or a full one (its fill and end
            // are 0 when it has none).
            "rcons" => {
                self.e(tst_low(1, 3));
                self.b_cond(Cond::Ne, slow);
                self.e(cmp_imm(1, 8 * fixpt_heap::heap::REGION_SLOTS as u32));
                self.b_cond(Cond::Hs, slow);
                self.e(ldr(X13, ST, off(offset_of!(State, regions))));
                self.e(add_lsl(X13, X13, 1, 1));
                self.e(ldp(X14, X15, X13, 0));
                self.e(add_imm(X16, X14, 2));
                self.e(cmp(X16, X15));
                self.b_cond(Cond::Hi, slow);
                self.e(ldr(X15, ST, off(offset_of!(State, words))));
                self.e(add_lsl(X11, X15, X14, 3));
                self.e(stp(2, 3, X11, 0));
                self.e(str(X16, X13, 0));
                self.e(add_imm(RESULT, X11, TAG_PAIR as u32));
            }
            other => unreachable!("{other} is not done inline"),
        }
    }
}

/// A register word's machine code: its register entry first, then an
/// instruction's code after another; and where each cell's resume point
/// is (`-1` for none), for [`NativeMachine::install`].
pub fn assemble_register_word(heap: &Heap, rw: Value, far: [i64; 2]) -> Result<(Vec<u32>, Vec<i64>), String> {
    let fields = heap.bloblet_head(rw).fields;
    let cells: Vec<Value> = (WORD_CELL0..=fields).map(|k| heap.bloblet_slot(rw, k)).collect();
    let mut starts = vec![false; cells.len() + 1];
    let mut i = 0;
    while i < cells.len() {
        starts[i] = true;
        i += 1 + OPS[cells[i].as_fixnum() as usize].1;
    }
    let mut a = Asm::new();
    let labels: Vec<Label> = (0..=cells.len()).map(|_| a.label()).collect();
    let mut resume = vec![-1i64; cells.len()];
    let far_exit = a.exit_common;
    let near_exit = a.label();
    a.exit_common = near_exit;
    // The register entry.
    let entry = a.label();
    a.bind(entry);
    a.fuel();
    a.rs_limit();
    a.pool(fields);
    // Where a backward branch goes: a loop's head, 32-aligned (words are),
    // so that the loop's speed does not depend on where the word lands.
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
    let mut i = 0;
    while i < cells.len() {
        if loop_heads[i] {
            while a.here() % 8 != 0 {
                a.e(NOP);
            }
        }
        a.bind(labels[i]);
        let (name, n, _) = OPS[cells[i].as_fixnum() as usize];
        let o = |j: usize| cells[i + 1 + j];
        let f = |j: usize| WORD_CELL0 + i + 1 + j;
        let next = i + 1 + n;
        let k = |v: Value| v.as_fixnum() as usize;
        match name {
            "args" => {}
            "const" => {
                let v = o(0);
                if v.is_fixnum() || v.raw() & 7 == 3 {
                    a.es(&mov_imm64(RESULT, v.raw()));
                } else {
                    a.cell(RESULT, f(0), fields);
                }
            }
            "global" | "setglbl" => {
                a.cell(X16, f(0), fields);
                a.e(mov(X11, X16));
                a.e(if name == "global" { ldur(RESULT, X11, field_off(2)) } else { stur(RESULT, X11, field_off(2)) });
                if name == "setglbl" {
                    a.es(&card_mark(X11, field_off(2), ST, off(offset_of!(State, cards)), X13, X16));
                }
            }
            "reg" => a.e(mov(RESULT, reg(k(o(0))))),
            "setreg" => a.e(mov(reg(k(o(0))), RESULT)),
            "movereg" => a.e(mov(reg(k(o(1))), reg(k(o(0))))),
            "lexical" => {
                a.e(mov(X11, CLO));
                a.field_of(RESULT, X11, CLOSURE_FREE0 + k(o(0)));
            }
            // A frame of `m` slots, and below them the link: where a call
            // by `blr` returns to, which a call from this frame replaces.
            // The collector scans the frame, and the link reads as a
            // fixnum: every point a `blr` returns to is 8-aligned (as
            // Larceny aligns its return points), and a call no `blr` made
            // has 0 (the adapter).
            "save" => {
                let m = k(o(0));
                a.link = Some(m);
                a.sub_const(DSP, DSP, 8 * (m as u64 + 1));
                a.value(X15, Value::FALSE);
                for s in 1..=m {
                    a.e(str(X15, DSP, 8 * s as u32));
                }
                a.e(str(LR, DSP, 0));
                a.e(add_imm(FP, DSP, 8 * m as u32));
                a.ds_limit();
            }
            "pop" => {
                let m = k(o(0));
                a.e(add_imm(DSP, DSP, 8 * (m as u32 + 1)));
            }
            "stack" => a.slot(RESULT, k(o(0)), false),
            "setstk" => a.slot(RESULT, k(o(0)), true),
            "load" => a.slot(reg(k(o(0))), k(o(1)), false),
            "store" => a.slot(reg(k(o(0))), k(o(1)), true),
            "op1" => match ROUTINES[k(o(0))].0 {
                r @ ("pair-car" | "pair-cdr") => {
                    // A list may be `nil`: `car` of it traps.
                    a.e(and_low(X13, RESULT, 3));
                    a.e(cmp_imm(X13, TAG_PAIR as u32));
                    a.trap_if(Cond::Ne, Trap::Type { routine: if r == "pair-car" { "pair-car" } else { "pair-cdr" } });
                    a.e(ldur(RESULT, RESULT, if r == "pair-car" { -1 } else { 7 }));
                }
                r => return Err(format!("op1 {r} in register code")),
            },
            "op2" | "op2imm" => {
                let other = if name == "op2" {
                    reg(k(o(1)))
                } else {
                    let v = o(1);
                    if v.is_fixnum() || v.raw() & 7 == 3 {
                        a.es(&mov_imm64(X13, v.raw()));
                    } else {
                        a.cell(X13, f(1), fields);
                    }
                    X13
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
                    a.e(orr(X15, RESULT, other));
                    a.e(tst_low(X15, 3));
                    a.b_cond(Cond::Ne, slow);
                }
                match r {
                    "int-add" | "int-sub" => {
                        a.e(if r == "int-add" { adds(X15, RESULT, other) } else { subs(X15, RESULT, other) });
                        a.b_cond(Cond::Vs, slow);
                        a.e(mov(RESULT, X15));
                    }
                    "int-less" | "eq" | "int-eq" => {
                        a.e(cmp(RESULT, other));
                        a.value(X16, Value::TRUE);
                        a.value(X15, Value::FALSE);
                        a.e(csel(RESULT, X16, X15, if r == "int-less" { Cond::Lt } else { Cond::Eq }));
                    }
                    r => return Err(format!("{name} {r} in register code")),
                }
                if let Some(pn) = slow_prim {
                    a.b(done);
                    a.bind(slow);
                    let p = fixpt_runtime::PRIMITIVES.iter().position(|d| d.name == pn).expect("a primitive");
                    a.pure_call(p, other);
                    a.bind(done);
                }
            }
            // A primitive that never collects: called with no safepoint,
            // REG1…REG8 and the link kept on the machine stack around it.
            "prim1" | "prim2" | "prim2imm" => {
                let p = k(o(0));
                if !fixpt_runtime::PRIMITIVES.get(p).is_some_and(|d| fixpt_runtime::never_collects(d.name)) {
                    return Err(format!("`{name}` of primitive {p}, which may collect"));
                }
                let y = match name {
                    "prim2" => reg(k(o(1))),
                    "prim2imm" => {
                        let v = o(1);
                        if v.is_fixnum() || v.raw() & 7 == 3 {
                            a.es(&mov_imm64(X13, v.raw()));
                        } else {
                            a.cell(X13, f(1), fields);
                        }
                        X13
                    }
                    _ => X13,
                };
                a.pure_call(p, y);
            }
            "field" => {
                a.field_of(RESULT, RESULT, k(o(0)));
            }
            "setfield" => {
                a.e(mov(X11, RESULT));
                let off = field_off(k(o(0)));
                if off >= -256 {
                    a.e(stur(reg(k(o(1))), X11, off));
                    a.es(&card_mark(X11, off, ST, super::off(offset_of!(State, cards)), X13, X16));
                } else {
                    a.sub_const(X16, X11, -off as u64);
                    a.e(str(reg(k(o(1))), X16, 0));
                    a.es(&card_mark(X16, 0, ST, super::off(offset_of!(State, cards)), X13, X16));
                }
            }
            "prim" | "lambda" | "cellular" => {
                let (count, routine_n, at) = match name {
                    "prim" => (k(o(1)), routine("prim"), f(0)),
                    "lambda" => (k(o(1)), routine("closure"), f(0)),
                    _ => (k(o(1)), k(o(0)) as u64, WORD_CELL0 + next),
                };
                // Some are done here, when they can be: the call-out is then
                // only the way for what cannot (a full heap, an index out of
                // range, which it reports).
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
                    ("prim", 2) if prim_named(k(o(0)), "%fx26-char-in?") => Some("char-in"),
                    ("prim", 2) if prim_named(k(o(0)), "string=?") => Some("string="),
                    ("prim", 2) if prim_named(k(o(0)), "modulo") => Some("modulo"),
                    ("prim", 1) if prim_named(k(o(0)), "%make-box") => Some("box"),
                    ("prim", 2) if prim_named(k(o(0)), "%region-new") => Some("rnew"),
                    ("prim", 1) if prim_named(k(o(0)), "%region-make-icell") => Some("ricell"),
                    ("prim", c) if c >= 2 && c <= REGS && prim_named(k(o(0)), "%region-closure") => Some("region-closure"),
                    ("prim", c) if c >= 1 && prim_named(k(o(0)), "%make-frozen") => Some("frozen"),
                    ("lambda", _) => Some("closure"),
                    _ => None,
                };
                if let Some(what) = inline.filter(|_| count <= REGS) {
                    a.inline_op(what, count, f(0), fields, slow);
                    a.b(done);
                }
                a.bind(slow);
                if a.link.is_none() {
                    // A leaf's link, kept while it calls out (`relink`).
                    a.e(str(LR, ST, off(offset_of!(State, leaf_link))));
                }
                a.push_regs(count);
                a.r_callout(routine_n, at);
                resume[next] = a.here() as i64;
                a.resumed(fields);
                a.bind(done);
            }
            "invoke" | "tailinvoke" => {
                let tail = name == "tailinvoke";
                let count = k(o(0));
                let cellular = a.label();
                // The callee, its word, and the word's twin.
                a.e(mov(W, RESULT));
                a.e(mov(X11, W));
                a.e(ldur(X12, X11, field_off(CLOSURE_WORD)));
                a.e(mov(X11, X12));
                a.e(ldur(X10, X11, field_off(WORD_TWIN)));
                a.value(X15, Value::FALSE);
                a.e(cmp(X10, X15));
                a.b_cond(Cond::Eq, cellular);
                a.e(mov(X11, X10));
                a.e(ldur(X15, X11, field_off(WORD_ENTRY)));
                a.cbz(X15, cellular);
                // Register code: the arguments stay where they are. A call
                // pushes a return entry marked as one `blr` made (its `8k`
                // negated), so that the callee returns by `ret`, with the
                // value in `RESULT`. The entry is loaded last: making the
                // return entry may need X16 for a large offset.
                let back = a.label();
                if !tail {
                    a.ip_at(WORD_CELL0 + next);
                    a.push_return_marked();
                }
                a.e(ldr_reg(X16, TABLE, X15));
                a.e(mov(CLO, W));
                a.e(mov(CUR, X10));
                if tail {
                    a.e(br(X16));
                } else {
                    // The instruction after the `blr` 8-aligned (words are).
                    if a.here() % 2 == 0 {
                        a.e(NOP);
                    }
                    a.e(blr(X16));
                    a.b(back);
                }
                // Stack code: the arguments as its frame. It returns the
                // stack's way, so an entry this procedure was called with
                // by `blr` is unmarked first, in a tail call.
                a.bind(cellular);
                a.fuel();
                a.push_regs(count);
                a.ds_limit();
                a.rs_limit();
                if tail {
                    a.unmark_return();
                } else {
                    a.ip_at(WORD_CELL0 + next);
                    a.push_return();
                }
                if count == 0 {
                    a.e(sub_imm(FP, DSP, 8));
                } else {
                    a.e(add_imm(FP, DSP, 8 * (count as u32 - 1)));
                }
                a.e(mov(CLO, W));
                a.e(mov(CUR, X12));
                a.ip_at(WORD_CELL0);
                a.e(movz(X13, (8 * WORD_CELL0) as u32, 0));
                a.enter_cur(X13);
                if !tail {
                    // Returned to the stack's way (the resume table), the
                    // value on the data stack; or by `ret`, in `RESULT`.
                    resume[next] = a.here() as i64;
                    a.e(ldr_post(RESULT, DSP, 8));
                    a.bind(back);
                    a.pool(fields);
                    a.relink();
                }
            }
            // A call of the procedure itself: its closure is the one running
            // and its word this one, so a `bl` to this word's own entry, as
            // `invoke` calls register code, with the same resume points.
            "invokeself" => {
                let back = a.label();
                a.ip_at(WORD_CELL0 + next);
                a.push_return_marked();
                if a.here() % 2 == 0 {
                    a.e(NOP);
                }
                a.bl_to(entry);
                a.b(back);
                resume[next] = a.here() as i64;
                a.e(ldr_post(RESULT, DSP, 8));
                a.bind(back);
                a.pool(fields);
                a.relink();
            }
            // To an entry a `blr` pushed: the caller's registers from it,
            // and back to the link. By `br`, not `ret`: `ret` is predicted
            // from the processor's stack of return addresses, which a deep
            // recursion (a `map` of a long list) overflows, and then nearly
            // every return mispredicts (`docs/performance.md`). To any other
            // entry, the stack's way.
            "return" => {
                let stack = a.label();
                a.e(ldr(X13, RSP, 8));
                a.e(cmp_imm(X13, 0));
                a.b_cond(Cond::Ge, stack);
                a.e(ldp_post(CUR, X13, RSP, 16));
                a.e(ldp_post(X14, CLO, RSP, 16));
                a.fp_decode(X14);
                a.e(br(LR));
                a.bind(stack);
                a.e(str_pre(RESULT, DSP, -8));
                a.pop_return_of(true);
            }
            "branch" | "branchf" | "brancht" => {
                let to = (i as i64 + 2 + o(0).as_fixnum()) as usize;
                if name != "branch" {
                    a.value(X16, Value::FALSE);
                    a.e(cmp(RESULT, X16));
                    a.b_cond(if name == "branchf" { Cond::Eq } else { Cond::Ne }, labels[to]);
                } else {
                    if to <= i {
                        a.fuel();
                    }
                    a.b(labels[to]);
                }
            }
            // The global's value's field 2: a cellular closure's word, or a
            // native closure's code, whose field 2 is the word it was
            // compiled from (`CODE_SOURCE`); a word's field 2 is no word.
            "global-guard" => {
                let to = (i as i64 + 4 + o(2).as_fixnum()) as usize;
                let held = a.label();
                a.cell(X16, f(0), fields);
                a.e(ldur(X11, X16, field_off(2)));
                a.e(ldur(X12, X11, field_off(CLOSURE_WORD)));
                a.cell(X16, f(1), fields);
                a.e(cmp(X12, X16));
                a.b_cond(Cond::Eq, held);
                a.e(ldur(X12, X12, field_off(fixpt_heap::layout::cellular::CODE_SOURCE)));
                a.e(cmp(X12, X16));
                a.b_cond(Cond::Ne, labels[to]);
                a.bind(held);
            }
            other => return Err(format!("`{other}` in register code")),
        }
        i = next;
    }
    a.bind(labels[cells.len()]);
    // Out of the way of the code that runs: the traps, and a jump to the
    // machine's exit, which may be too far for a conditional branch.
    a.flush_stubs();
    a.bind(near_exit);
    a.b(far_exit);
    a.exit_common = far_exit;
    // The machine's common trap and exit, through the state, as a word's
    // (`assemble_word`): no branch leaves this code.
    let [tc, ec] = [a.trap_common, a.exit_common];
    a.bind(tc);
    a.e(ldr(X16, ST, off(offset_of!(State, trap))));
    a.e(br(X16));
    a.bind(ec);
    a.e(ldr(X16, ST, off(offset_of!(State, exit))));
    a.e(br(X16));
    let _ = (far, far_exit, starts, REGS);
    Ok((a.finish(), resume))
}

/// With `FIXPT_REGCODE_DUMP=file`, each register word's machine code is
/// appended to `file`, for looking at: a line of its name and where it
/// starts in the code space, then its instructions, one to a line, as
/// `.inst` directives an assembler takes back.
fn dump(heap: &Heap, rw: Value, at: usize, code: &[u32]) {
    let Ok(file) = std::env::var("FIXPT_REGCODE_DUMP") else { return };
    let name = heap.symbol_name(heap.bloblet_slot(rw, WORD_NAME));
    let mut text = format!("// {name} at {at:#x}\n");
    for w in code {
        text.push_str(&format!("  .inst {w:#010x}\n"));
    }
    use std::io::Write;
    if let Ok(mut f) = std::fs::OpenOptions::new().create(true).append(true).open(file) {
        let _ = f.write_all(text.as_bytes());
    }
}

/// The entry a stack-code caller takes into a word with register code: the
/// `n` arguments from its frame into registers, the frame dropped, and on
/// to the register word's entry, native slot `slot`.
pub fn assemble_adapter(n: usize, slot: usize) -> Vec<u32> {
    let mut a = Asm::new();
    for i in 0..n {
        a.e(ldur(reg(i + 1), FP, -8 * i as i64));
    }
    a.e(add_imm(DSP, FP, 8));
    a.e(mov(X11, CUR));
    a.e(ldur(CUR, X11, field_off(WORD_TWIN)));
    // Past 4096 slots, the offset is too far for one `ldr`.
    let off = 8 * slot as u64;
    if off < 32768 {
        a.e(ldr(X16, TABLE, off as u32));
    } else {
        a.es(&mov_imm64(X16, off));
        a.e(ldr_reg(X16, TABLE, X16));
    }
    // No `blr` made this call: the link the callee keeps is a fixnum, 0.
    a.e(mov(LR, XZR));
    a.e(br(X16));
    a.finish()
}

impl NativeMachine {
    /// Compile `word`'s register code, if it has some and it is not yet
    /// compiled: the register word's code in a native slot of its own, and
    /// `word` entered through an adapter to it. Whether it did.
    pub fn compile_register_word(&mut self, heap: &mut Heap, word: Value) -> Result<bool, String> {
        let rw = heap.bloblet_slot(word, WORD_TWIN);
        if !heap.is_register_word(rw) || heap.bloblet_slot(rw, WORD_ENTRY).as_fixnum() != 0 {
            return Ok(false);
        }
        // A variadic procedure's register code (`vargs`) is for native code,
        // which passes the count in a register; here, its stack code, which
        // finds the count from its frame.
        if heap.bloblet_slot(rw, WORD_CELL0).as_fixnum() as usize == fixpt_heap::layout::regcode::op("vargs") {
            self.compile_word(heap, word)?;
            return Ok(true);
        }
        let (code, _) = assemble_register_word(heap, rw, [0, 0])?;
        let (at, far) = self.reserve_collecting(heap, code.len())?;
        let (code, resume) = assemble_register_word(heap, rw, far)?;
        dump(heap, rw, at, &code);
        self.install(heap, rw, at, &code, &resume)?;
        let slot = heap.bloblet_slot(rw, WORD_ENTRY).as_fixnum() as usize;
        let n = heap.bloblet_slot(rw, WORD_CELL0 + 1).as_fixnum() as usize;
        // Past `REGS` arguments stack code runs the word as stack code:
        // entering register code, it would have to make a list of the rest.
        if n > REGS {
            self.compile_word(heap, word)?;
            return Ok(true);
        }
        let adapter = assemble_adapter(n, slot);
        let (at, _) = self.reserve_collecting(heap, adapter.len())?;
        let cells = heap.bloblet_head(word).fields + 1 - WORD_CELL0;
        let mut starts = vec![-1i64; cells];
        starts[0] = 0;
        self.install(heap, word, at, &adapter, &starts)?;
        Ok(true)
    }
}
