//! An x86_64 encoder: only the instructions the native core uses, each one a
//! function returning its bytes. Registers are numbered 0–15 as the
//! hardware numbers them (`rax` 0 … `r15` 15); every operation is on 64
//! bits unless its name says otherwise.
//!
//! Every encoding is checked against the system assembler in
//! `tests/x86_64.rs`, as `arm64.rs`'s are: so this is the oracle for an
//! encoder written in FX-26 later, and it answers to `as` now.
//!
//! Instructions vary in length here, from 1 byte to 10, so each is an
//! [`Ins`]: its bytes, at most 15, which is the most x86_64 allows.

pub mod disasm;

pub type Reg = u8;

pub const RAX: Reg = 0;
pub const RCX: Reg = 1;
pub const RDX: Reg = 2;
pub const RBX: Reg = 3;
pub const RSP: Reg = 4;
pub const RBP: Reg = 5;
pub const RSI: Reg = 6;
pub const RDI: Reg = 7;
pub const R8: Reg = 8;
pub const R9: Reg = 9;
pub const R10: Reg = 10;
pub const R11: Reg = 11;
pub const R12: Reg = 12;
pub const R13: Reg = 13;
pub const R14: Reg = 14;
pub const R15: Reg = 15;

/// Register names, by number, as the assembler writes them.
pub const NAMES: [&str; 16] = ["rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"];

/// Condition codes, for `jcc`, `cmovcc` and `setcc`, by the hardware's
/// numbers. After `cmp a, b`: `B`/`Ae`/`Be`/`A` compare `a` with `b`
/// unsigned, `L`/`Ge`/`Le`/`G` signed.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Cond {
    O = 0,
    No = 1,
    /// Unsigned <.
    B = 2,
    /// Unsigned ≥.
    Ae = 3,
    E = 4,
    Ne = 5,
    /// Unsigned ≤.
    Be = 6,
    /// Unsigned >.
    A = 7,
    S = 8,
    Ns = 9,
    P = 10,
    Np = 11,
    L = 12,
    Ge = 13,
    Le = 14,
    G = 15,
}

impl Cond {
    /// The condition that holds where this one does not.
    pub fn not(self) -> Cond {
        Cond::from_bits(self as u8 ^ 1)
    }
    pub fn from_bits(c: u8) -> Cond {
        use Cond::*;
        [O, No, B, Ae, E, Ne, Be, A, S, Ns, P, Np, L, Ge, Le, G][(c & 15) as usize]
    }
    /// Its name in a mnemonic: `j{name}`, `cmov{name}`.
    pub fn name(self) -> &'static str {
        ["o", "no", "b", "ae", "e", "ne", "be", "a", "s", "ns", "p", "np", "l", "ge", "le", "g"][self as usize]
    }
}

/// One instruction's bytes.
#[derive(Copy, Clone, PartialEq, Eq)]
pub struct Ins {
    bytes: [u8; 15],
    len: u8,
}

impl Ins {
    fn new() -> Ins {
        Ins { bytes: [0; 15], len: 0 }
    }
    fn b(&mut self, b: u8) -> &mut Ins {
        self.bytes[self.len as usize] = b;
        self.len += 1;
        self
    }
    fn i8(&mut self, v: i8) -> &mut Ins {
        self.b(v as u8)
    }
    fn i32(&mut self, v: i32) -> &mut Ins {
        for b in v.to_le_bytes() {
            self.b(b);
        }
        self
    }
    fn u64(&mut self, v: u64) -> &mut Ins {
        for b in v.to_le_bytes() {
            self.b(b);
        }
        self
    }
}

impl std::ops::Deref for Ins {
    type Target = [u8];
    fn deref(&self) -> &[u8] {
        &self.bytes[..self.len as usize]
    }
}

impl std::fmt::Debug for Ins {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, b) in self.iter().enumerate() {
            write!(f, "{}{b:02x}", if i == 0 { "" } else { " " })?;
        }
        Ok(())
    }
}

/// A memory operand: `[base + index * scale + disp]`.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Mem {
    pub base: Reg,
    /// The index and its scale, 1, 2, 4 or 8; never `rsp`.
    pub index: Option<(Reg, u8)>,
    pub disp: i32,
}

/// `[base + disp]`.
pub fn m(base: Reg, disp: i32) -> Mem {
    Mem { base, index: None, disp }
}

/// `[base + index * scale + disp]`.
pub fn mi(base: Reg, index: Reg, scale: u8, disp: i32) -> Mem {
    assert!(index != RSP, "rsp is no index");
    assert!(matches!(scale, 1 | 2 | 4 | 8), "no scale {scale}");
    Mem { base, index: Some((index, scale)), disp }
}

fn reg(r: Reg) -> u8 {
    debug_assert!(r < 16, "no register {r}");
    r
}

/// A REX prefix: `w` for 64 bits, and the high bits of the ModRM `reg`
/// field, the SIB index and the ModRM `rm` (or SIB base). Left out when
/// nothing needs it, unless `force` (byte registers past `bl`).
fn rex(i: &mut Ins, w: bool, r: u8, x: u8, b: u8) {
    let v = 0x40 | (w as u8) << 3 | (r >> 3) << 2 | (x >> 3) << 1 | (b >> 3);
    if v != 0x40 {
        i.b(v);
    }
}

/// The REX prefix, opcode and ModRM byte of an instruction on two
/// registers: `field` in ModRM's `reg`, `rm` in its `rm`.
fn op_rr(w: bool, opcode: &[u8], field: u8, rm: Reg) -> Ins {
    let mut i = Ins::new();
    rex(&mut i, w, field, 0, reg(rm));
    for &b in opcode {
        i.b(b);
    }
    i.b(0xC0 | (field & 7) << 3 | (rm & 7));
    i
}

/// The same with a memory operand in `rm`.
fn op_rm(w: bool, opcode: &[u8], field: u8, mem: Mem) -> Ins {
    let mut i = Ins::new();
    let x = mem.index.map_or(0, |(r, _)| reg(r));
    rex(&mut i, w, field, x, reg(mem.base));
    for &b in opcode {
        i.b(b);
    }
    modrm_mem(&mut i, field, mem);
    i
}

/// ModRM, SIB and displacement for `mem`, with `field` in ModRM's `reg`.
fn modrm_mem(i: &mut Ins, field: u8, mem: Mem) {
    let base = mem.base & 7;
    // `rbp` and `r13` as a base with no displacement mean something else
    // (rip-relative, or no base): give them a zero byte of one.
    let md = if mem.disp == 0 && base != 5 {
        0
    } else if i8::try_from(mem.disp).is_ok() {
        1
    } else {
        2
    };
    match mem.index {
        None if base != 4 => {
            i.b(md << 6 | (field & 7) << 3 | base);
        }
        index => {
            // `rsp` and `r12` as a base need a SIB byte; so does an index.
            let (ix, scale) = index.map_or((4, 1), |(r, s)| (r & 7, s));
            i.b(md << 6 | (field & 7) << 3 | 4);
            i.b((scale.trailing_zeros() as u8) << 6 | ix << 3 | base);
        }
    }
    match md {
        1 => {
            i.i8(mem.disp as i8);
        }
        2 => {
            i.i32(mem.disp);
        }
        _ => {}
    }
}

/// The same with `[rip + disp]` in `rm`: `disp` from the end of the
/// instruction, its last four bytes.
fn op_rip(w: bool, opcode: &[u8], field: u8, disp: i32) -> Ins {
    let mut i = Ins::new();
    rex(&mut i, w, field, 0, 0);
    for &b in opcode {
        i.b(b);
    }
    i.b((field & 7) << 3 | 5);
    i.i32(disp);
    i
}

// ---------------------------------------------------------------- moves

/// `mov d, [rip + disp]`: a word `disp` bytes past this instruction's end.
pub fn load_rip(d: Reg, disp: i32) -> Ins {
    op_rip(true, &[0x8B], d, disp)
}

/// `lea d, [rip + disp]`.
pub fn lea_rip(d: Reg, disp: i32) -> Ins {
    op_rip(true, &[0x8D], d, disp)
}

/// `mov d, s`.
pub fn mov(d: Reg, s: Reg) -> Ins {
    op_rr(true, &[0x89], s, d)
}

/// `mov d, [mem]`.
pub fn load(d: Reg, mem: Mem) -> Ins {
    op_rm(true, &[0x8B], d, mem)
}

/// `mov [mem], s`.
pub fn store(mem: Mem, s: Reg) -> Ins {
    op_rm(true, &[0x89], s, mem)
}

/// `mov qword [mem], imm`, sign-extended.
pub fn store_imm(mem: Mem, imm: i32) -> Ins {
    let mut i = op_rm(true, &[0xC7], 0, mem);
    i.i32(imm);
    i
}

/// `mov d32, [mem]`: 32 bits, zero-extended.
pub fn load32(d: Reg, mem: Mem) -> Ins {
    op_rm(false, &[0x8B], d, mem)
}

/// `mov [mem], s32`: the low 32 bits.
pub fn store32(mem: Mem, s: Reg) -> Ins {
    op_rm(false, &[0x89], s, mem)
}

/// `movsxd d, dword [mem]`: 32 bits, sign-extended.
pub fn load32s(d: Reg, mem: Mem) -> Ins {
    op_rm(true, &[0x63], d, mem)
}

/// `movzx d, byte [mem]`.
pub fn load8(d: Reg, mem: Mem) -> Ins {
    op_rm(false, &[0x0F, 0xB6], d, mem)
}

/// `mov d, imm` in as few bytes as do it: `mov d32, imm` when it fits 32
/// bits unsigned (zero-extended), `mov d, imm` sign-extended when it
/// fits 32 bits signed, else `movabs`. Unlike `xor`, none touches the flags.
pub fn mov_imm(d: Reg, imm: u64) -> Ins {
    if let Ok(v) = u32::try_from(imm) {
        let mut i = Ins::new();
        rex(&mut i, false, 0, 0, reg(d));
        i.b(0xB8 + (d & 7));
        i.i32(v as i32);
        i
    } else if let Ok(v) = i32::try_from(imm as i64) {
        let mut i = op_rr(true, &[0xC7], 0, d);
        i.i32(v);
        i
    } else {
        mov_imm64(d, imm)
    }
}

/// `movabs d, imm`: always the whole 10 bytes, so that it can be patched.
pub fn mov_imm64(d: Reg, imm: u64) -> Ins {
    let mut i = Ins::new();
    rex(&mut i, true, 0, 0, reg(d));
    i.b(0xB8 + (d & 7));
    i.u64(imm);
    i
}

/// `lea d, [mem]`.
pub fn lea(d: Reg, mem: Mem) -> Ins {
    op_rm(true, &[0x8D], d, mem)
}

/// `cmov{c} d, s`.
pub fn cmov(c: Cond, d: Reg, s: Reg) -> Ins {
    op_rr(true, &[0x0F, 0x40 | c as u8], d, s)
}

/// `cmov{c} d, [mem]`.
pub fn cmov_m(c: Cond, d: Reg, mem: Mem) -> Ins {
    op_rm(true, &[0x0F, 0x40 | c as u8], d, mem)
}

// ----------------------------------------------------------- arithmetic

/// The eight arithmetic operations of the `/digit` group, by its numbers.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Alu {
    Add = 0,
    Or = 1,
    Adc = 2,
    Sbb = 3,
    And = 4,
    Sub = 5,
    Xor = 6,
    Cmp = 7,
}

impl Alu {
    pub fn name(self) -> &'static str {
        ["add", "or", "adc", "sbb", "and", "sub", "xor", "cmp"][self as usize]
    }
}

/// `{op} d, s`.
pub fn alu(op: Alu, d: Reg, s: Reg) -> Ins {
    op_rr(true, &[(op as u8) << 3 | 1], s, d)
}

/// `{op} d, [mem]`.
pub fn alu_rm(op: Alu, d: Reg, mem: Mem) -> Ins {
    op_rm(true, &[(op as u8) << 3 | 3], d, mem)
}

/// `{op} [mem], s`.
pub fn alu_mr(op: Alu, mem: Mem, s: Reg) -> Ins {
    op_rm(true, &[(op as u8) << 3 | 1], s, mem)
}

/// `{op} d, imm`, sign-extended: a byte of it when it fits one, and the
/// short form for `rax` otherwise, as the assembler chooses.
pub fn alu_imm(op: Alu, d: Reg, imm: i32) -> Ins {
    if let Ok(v) = i8::try_from(imm) {
        let mut i = op_rr(true, &[0x83], op as u8, d);
        i.i8(v);
        i
    } else if d == RAX {
        let mut i = Ins::new();
        i.b(0x48).b((op as u8) << 3 | 5).i32(imm);
        i
    } else {
        let mut i = op_rr(true, &[0x81], op as u8, d);
        i.i32(imm);
        i
    }
}

/// `{op} qword [mem], imm`, sign-extended.
pub fn alu_mi(op: Alu, mem: Mem, imm: i32) -> Ins {
    if let Ok(v) = i8::try_from(imm) {
        let mut i = op_rm(true, &[0x83], op as u8, mem);
        i.i8(v);
        i
    } else {
        let mut i = op_rm(true, &[0x81], op as u8, mem);
        i.i32(imm);
        i
    }
}

pub fn add(d: Reg, s: Reg) -> Ins {
    alu(Alu::Add, d, s)
}
pub fn sub(d: Reg, s: Reg) -> Ins {
    alu(Alu::Sub, d, s)
}
pub fn and(d: Reg, s: Reg) -> Ins {
    alu(Alu::And, d, s)
}
pub fn or(d: Reg, s: Reg) -> Ins {
    alu(Alu::Or, d, s)
}
pub fn xor(d: Reg, s: Reg) -> Ins {
    alu(Alu::Xor, d, s)
}
pub fn cmp(a: Reg, b: Reg) -> Ins {
    alu(Alu::Cmp, a, b)
}
pub fn add_imm(d: Reg, imm: i32) -> Ins {
    alu_imm(Alu::Add, d, imm)
}
pub fn sub_imm(d: Reg, imm: i32) -> Ins {
    alu_imm(Alu::Sub, d, imm)
}
pub fn and_imm(d: Reg, imm: i32) -> Ins {
    alu_imm(Alu::And, d, imm)
}
pub fn cmp_imm(a: Reg, imm: i32) -> Ins {
    alu_imm(Alu::Cmp, a, imm)
}

/// `test a, b`.
pub fn test(a: Reg, b: Reg) -> Ins {
    op_rr(true, &[0x85], b, a)
}

/// `test a32, imm`: the low 32 bits of `a`, which is all a tag test needs.
pub fn test_imm(a: Reg, imm: u32) -> Ins {
    let mut i = if a == RAX {
        let mut i = Ins::new();
        i.b(0xA9);
        i
    } else {
        op_rr(false, &[0xF7], 0, a)
    };
    i.i32(imm as i32);
    i
}

/// `imul d, s`: the low 64 bits; `o` if the product does not fit.
pub fn imul(d: Reg, s: Reg) -> Ins {
    op_rr(true, &[0x0F, 0xAF], d, s)
}

/// `neg d`.
pub fn neg(d: Reg) -> Ins {
    op_rr(true, &[0xF7], 3, d)
}

/// `neg qword [mem]`.
pub fn neg_m(mem: Mem) -> Ins {
    op_rm(true, &[0xF7], 3, mem)
}

/// `not d`.
pub fn not(d: Reg) -> Ins {
    op_rr(true, &[0xF7], 2, d)
}

/// `cqo`: `rdx` the sign of `rax`.
pub fn cqo() -> Ins {
    let mut i = Ins::new();
    i.b(0x48).b(0x99);
    i
}

/// `idiv s`: `rdx:rax` by `s`, the quotient in `rax`, the remainder in `rdx`.
pub fn idiv(s: Reg) -> Ins {
    op_rr(true, &[0xF7], 7, s)
}

/// Shifts, by their `/digit`.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Shift {
    Shl = 4,
    Shr = 5,
    Sar = 7,
}

impl Shift {
    pub fn name(self) -> &'static str {
        match self {
            Shift::Shl => "shl",
            Shift::Shr => "shr",
            Shift::Sar => "sar",
        }
    }
}

/// `{op} d, imm`.
pub fn shift_imm(op: Shift, d: Reg, imm: u8) -> Ins {
    assert!(imm < 64, "a shift of {imm}");
    if imm == 1 {
        op_rr(true, &[0xD1], op as u8, d)
    } else {
        let mut i = op_rr(true, &[0xC1], op as u8, d);
        i.b(imm);
        i
    }
}

/// `{op} d, cl`.
pub fn shift_cl(op: Shift, d: Reg) -> Ins {
    op_rr(true, &[0xD3], op as u8, d)
}

pub fn shl_imm(d: Reg, imm: u8) -> Ins {
    shift_imm(Shift::Shl, d, imm)
}
pub fn shr_imm(d: Reg, imm: u8) -> Ins {
    shift_imm(Shift::Shr, d, imm)
}
pub fn sar_imm(d: Reg, imm: u8) -> Ins {
    shift_imm(Shift::Sar, d, imm)
}

/// A REX prefix for an instruction on byte register `b8` (and `r` in
/// ModRM's `reg`): wherever one is needed, and for 4 to 7, so that they
/// name `spl` … `dil`, not `ah` … `bh`.
fn rex_byte(i: &mut Ins, r: u8, b8: u8) {
    if r >= 8 || b8 >= 4 {
        i.b(0x40 | (r >> 3) << 2 | (b8 >> 3));
    }
}

/// `movzx d32, s8`: the low byte of `s`, zero-extended.
pub fn movzx8(d: Reg, s: Reg) -> Ins {
    let mut i = Ins::new();
    rex_byte(&mut i, d, s);
    i.b(0x0F).b(0xB6).b(0xC0 | (d & 7) << 3 | (s & 7));
    i
}

/// `set{c} d8`, the byte register.
pub fn setcc(c: Cond, d: Reg) -> Ins {
    let mut i = Ins::new();
    rex_byte(&mut i, 0, d);
    i.b(0x0F).b(0x90 | c as u8).b(0xC0 | (d & 7));
    i
}

// -------------------------------------------------------------- control

/// `jmp rel32`: `rel` from the end of the instruction, 5 bytes long.
pub fn jmp(rel: i32) -> Ins {
    let mut i = Ins::new();
    i.b(0xE9).i32(rel);
    i
}

/// `jmp rel8`: 2 bytes.
pub fn jmp8(rel: i8) -> Ins {
    let mut i = Ins::new();
    i.b(0xEB).i8(rel);
    i
}

/// `j{c} rel32`: 6 bytes.
pub fn jcc(c: Cond, rel: i32) -> Ins {
    let mut i = Ins::new();
    i.b(0x0F).b(0x80 | c as u8).i32(rel);
    i
}

/// `j{c} rel8`: 2 bytes.
pub fn jcc8(c: Cond, rel: i8) -> Ins {
    let mut i = Ins::new();
    i.b(0x70 | c as u8).i8(rel);
    i
}

/// `call rel32`: 5 bytes.
pub fn call(rel: i32) -> Ins {
    let mut i = Ins::new();
    i.b(0xE8).i32(rel);
    i
}

/// `jmp s`.
pub fn jmp_r(s: Reg) -> Ins {
    op_rr(false, &[0xFF], 4, s)
}

/// `jmp [mem]`.
pub fn jmp_m(mem: Mem) -> Ins {
    op_rm(false, &[0xFF], 4, mem)
}

/// `call s`.
pub fn call_r(s: Reg) -> Ins {
    op_rr(false, &[0xFF], 2, s)
}

/// `call [mem]`.
pub fn call_m(mem: Mem) -> Ins {
    op_rm(false, &[0xFF], 2, mem)
}

/// `push s`.
pub fn push(s: Reg) -> Ins {
    let mut i = Ins::new();
    rex(&mut i, false, 0, 0, reg(s));
    i.b(0x50 + (s & 7));
    i
}

/// `push qword [mem]`.
pub fn push_m(mem: Mem) -> Ins {
    op_rm(false, &[0xFF], 6, mem)
}

/// `pop qword [mem]`.
pub fn pop_m(mem: Mem) -> Ins {
    op_rm(false, &[0x8F], 0, mem)
}

/// `pop d`.
pub fn pop(d: Reg) -> Ins {
    let mut i = Ins::new();
    rex(&mut i, false, 0, 0, reg(d));
    i.b(0x58 + (d & 7));
    i
}

/// `ret`.
pub fn ret() -> Ins {
    let mut i = Ins::new();
    i.b(0xC3);
    i
}

/// `ud2`: an undefined instruction, for code that must not be reached.
pub fn ud2() -> Ins {
    let mut i = Ins::new();
    i.b(0x0F).b(0x0B);
    i
}

/// `int3`: one byte.
pub fn int3() -> Ins {
    let mut i = Ins::new();
    i.b(0xCC);
    i
}

/// A no-op of `n` bytes, 1 to 9: the forms the manuals recommend.
pub fn nop(n: usize) -> Ins {
    const NOPS: [&[u8]; 9] = [
        &[0x90],
        &[0x66, 0x90],
        &[0x0F, 0x1F, 0x00],
        &[0x0F, 0x1F, 0x40, 0x00],
        &[0x0F, 0x1F, 0x44, 0x00, 0x00],
        &[0x66, 0x0F, 0x1F, 0x44, 0x00, 0x00],
        &[0x0F, 0x1F, 0x80, 0x00, 0x00, 0x00, 0x00],
        &[0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00],
        &[0x66, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00],
    ];
    assert!((1..=9).contains(&n), "no {n}-byte nop");
    let mut i = Ins::new();
    for &b in NOPS[n - 1] {
        i.b(b);
    }
    i
}

/// Bytes of no-ops, as few instructions as make `n`.
pub fn nops(n: usize) -> Vec<u8> {
    let mut out = Vec::with_capacity(n);
    let mut left = n;
    while left > 0 {
        let k = left.min(9);
        out.extend_from_slice(&nop(k));
        left -= k;
    }
    out
}

/// `arm64::card_mark`'s x86_64 form: mark the card of the word at
/// `[obj + disp]` in the biased card table at `[st + cards_off]`, as
/// `Heap::card_table_address` gives it: a card is 2^9 bytes, its mark a
/// byte of 1. `t1` and `t2` scratch.
pub fn card_mark(obj: Reg, disp: i32, st: Reg, cards_off: i32, t1: Reg, t2: Reg) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(&lea(t1, m(obj, disp)));
    out.extend_from_slice(&shr_imm(t1, 9));
    out.extend_from_slice(&load(t2, m(st, cards_off)));
    out.extend_from_slice(&store8_imm(mi(t2, t1, 1, 0), 1));
    out
}

/// `mov byte [mem], imm`.
pub fn store8_imm(mem: Mem, imm: u8) -> Ins {
    let mut i = op_rm(false, &[0xC6], 0, mem);
    i.b(imm);
    i
}

// ------------------------------------------------- narrower memory, `div`

/// `movzx d32, word [mem]`.
pub fn load16(d: Reg, mem: Mem) -> Ins {
    op_rm(false, &[0x0F, 0xB7], d, mem)
}

/// `mov byte [mem], s8`: a REX prefix for `sil` and `dil`, which name
/// something else without one.
pub fn store8(mem: Mem, s: Reg) -> Ins {
    let mut i = Ins::new();
    let x = mem.index.map_or(0, |(r, _)| reg(r));
    let v = 0x40 | (reg(s) >> 3) << 2 | (x >> 3) << 1 | (reg(mem.base) >> 3);
    if v != 0x40 || (4..8).contains(&s) {
        i.b(v);
    }
    i.b(0x88);
    modrm_mem(&mut i, s, mem);
    i
}

/// `mov word [mem], s16`.
pub fn store16(mem: Mem, s: Reg) -> Ins {
    prefixed(0x66, op_rm(false, &[0x89], s, mem))
}

/// `div s`: `rdx:rax` by `s`, unsigned, the quotient in `rax`, the
/// remainder in `rdx`.
pub fn div(s: Reg) -> Ins {
    op_rr(true, &[0xF7], 6, s)
}

/// `i` after a mandatory prefix, which goes before any REX.
fn prefixed(p: u8, i: Ins) -> Ins {
    let mut out = Ins::new();
    out.b(p);
    for &b in i.iter() {
        out.b(b);
    }
    out
}

// --------------------------------------------- scalar floating point (SSE)

/// An `xmm` register, by number.
pub type Xmm = u8;

/// An SSE instruction on two registers: `prefix` (0 for none), REX, `0F`
/// and `op`, with `field` in ModRM's `reg` and `rm` in its `rm`.
fn sse(prefix: u8, w: bool, op: &[u8], field: u8, rm: u8) -> Ins {
    let mut i = Ins::new();
    if prefix != 0 {
        i.b(prefix);
    }
    rex(&mut i, w, field, 0, rm);
    i.b(0x0F);
    for &b in op {
        i.b(b);
    }
    i.b(0xC0 | (field & 7) << 3 | (rm & 7));
    i
}

/// `movq x, r`: an `f64`'s bits into `x`.
pub fn movq_to_xmm(x: Xmm, r: Reg) -> Ins {
    sse(0x66, true, &[0x6E], x, r)
}

/// `movq r, x`.
pub fn movq_from_xmm(r: Reg, x: Xmm) -> Ins {
    sse(0x66, true, &[0x7E], x, r)
}

/// `movd x, r32`: an `f32`'s bits into `x`.
pub fn movd_to_xmm(x: Xmm, r: Reg) -> Ins {
    sse(0x66, false, &[0x6E], x, r)
}

/// `movd r32, x`, zero-extended.
pub fn movd_from_xmm(r: Reg, x: Xmm) -> Ins {
    sse(0x66, false, &[0x7E], x, r)
}

/// Scalar arithmetic, by its opcode.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Fop {
    Sqrt = 0x51,
    Add = 0x58,
    Mul = 0x59,
    Sub = 0x5C,
    Div = 0x5E,
}

impl Fop {
    pub fn name(self) -> &'static str {
        match self {
            Fop::Sqrt => "sqrt",
            Fop::Add => "add",
            Fop::Mul => "mul",
            Fop::Sub => "sub",
            Fop::Div => "div",
        }
    }
}

/// `{op}sd d, s` (`double`), or `{op}ss` (`!double`): `d op= s`, or for
/// `sqrt`, `d := sqrt s`.
pub fn fop(double: bool, op: Fop, d: Xmm, s: Xmm) -> Ins {
    sse(if double { 0xF2 } else { 0xF3 }, false, &[op as u8], d, s)
}

/// `ucomisd a, b` (`double`), or `ucomiss`: `a` against `b`, unordered
/// setting ZF, PF and CF.
pub fn ucomis(double: bool, a: Xmm, b: Xmm) -> Ins {
    sse(if double { 0x66 } else { 0 }, false, &[0x2E], a, b)
}

/// `cvtsi2sd x, r`: the signed integer in `r`, rounded as the mode says.
pub fn cvtsi2sd(x: Xmm, r: Reg) -> Ins {
    sse(0xF2, true, &[0x2A], x, r)
}

/// `cvttsd2si r, x`: truncated; out of range, `i64::MIN`.
pub fn cvttsd2si(r: Reg, x: Xmm) -> Ins {
    sse(0xF2, true, &[0x2C], r, x)
}

/// `roundsd d, s, mode` (`double`), or `roundss` (SSE4.1): 0 to nearest
/// (even), 1 down, 2 up, 3 toward zero.
pub fn round(double: bool, d: Xmm, s: Xmm, mode: u8) -> Ins {
    let mut i = sse(0x66, false, &[0x3A, if double { 0x0B } else { 0x0A }], d, s);
    i.b(mode);
    i
}
