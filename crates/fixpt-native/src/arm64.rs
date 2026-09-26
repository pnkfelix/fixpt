//! An arm64 encoder: only the instructions the native core uses, each one a
//! function returning its 32-bit word. Registers are numbered 0–30; 31 is
//! `sp` or `xzr`, as the instruction takes it.
//!
//! Every encoding is checked against the system assembler in
//! `tests/arm64.rs`, one instruction at a time. So this is the stage-0 oracle
//! for an encoder written in FX-26 later, and it answers to `as` now.

pub type Reg = u32;

pub const SP: Reg = 31;
pub const XZR: Reg = 31;

/// Condition codes, for `b.cond` and `csel`.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum Cond {
    Eq = 0,
    Ne = 1,
    Lt = 11,
    Ge = 10,
    Gt = 12,
    Le = 13,
}

fn r(x: Reg) -> u32 {
    debug_assert!(x <= 31, "no register x{x}");
    x
}

fn simm(v: i64, bits: u32) -> u32 {
    let lo = -(1i64 << (bits - 1));
    let hi = (1i64 << (bits - 1)) - 1;
    assert!(v >= lo && v <= hi, "{v} does not fit {bits} signed bits");
    (v as u32) & ((1u32 << bits) - 1)
}

// ------------------------------------------------------------ loads, stores

/// `ldr xt, [xn], #imm` — load, then add `imm` to `xn`.
pub fn ldr_post(t: Reg, n: Reg, imm: i64) -> u32 {
    0xF840_0400 | simm(imm, 9) << 12 | r(n) << 5 | r(t)
}
/// `ldr xt, [xn, #imm]!` — add `imm` to `xn`, then load.
pub fn ldr_pre(t: Reg, n: Reg, imm: i64) -> u32 {
    0xF840_0C00 | simm(imm, 9) << 12 | r(n) << 5 | r(t)
}
/// `str xt, [xn], #imm`.
pub fn str_post(t: Reg, n: Reg, imm: i64) -> u32 {
    0xF800_0400 | simm(imm, 9) << 12 | r(n) << 5 | r(t)
}
/// `str xt, [xn, #imm]!`.
pub fn str_pre(t: Reg, n: Reg, imm: i64) -> u32 {
    0xF800_0C00 | simm(imm, 9) << 12 | r(n) << 5 | r(t)
}
/// `ldr xt, [xn, #off]`, `off` a multiple of 8 in 0..32768.
pub fn ldr(t: Reg, n: Reg, off: u32) -> u32 {
    assert!(off.is_multiple_of(8) && off < 32768, "ldr offset {off}");
    0xF940_0000 | (off / 8) << 10 | r(n) << 5 | r(t)
}
/// `str xt, [xn, #off]`.
pub fn str(t: Reg, n: Reg, off: u32) -> u32 {
    assert!(off.is_multiple_of(8) && off < 32768, "str offset {off}");
    0xF900_0000 | (off / 8) << 10 | r(n) << 5 | r(t)
}
/// `ldur xt, [xn, #imm]` — any offset in −256..256.
pub fn ldur(t: Reg, n: Reg, imm: i64) -> u32 {
    0xF840_0000 | simm(imm, 9) << 12 | r(n) << 5 | r(t)
}
/// `stur xt, [xn, #imm]`.
pub fn stur(t: Reg, n: Reg, imm: i64) -> u32 {
    0xF800_0000 | simm(imm, 9) << 12 | r(n) << 5 | r(t)
}
/// `ldr xt, <label>` — a literal load, `words` instructions from here.
pub fn ldr_lit(t: Reg, words: i64) -> u32 {
    0x5800_0000 | simm(words, 19) << 5 | r(t)
}
/// `ldr xt, [xn, xm]`.
pub fn ldr_reg(t: Reg, n: Reg, m: Reg) -> u32 {
    0xF860_6800 | r(m) << 16 | r(n) << 5 | r(t)
}
/// `stp xt, xt2, [xn, #imm]!`, `imm` a multiple of 8.
pub fn stp_pre(t: Reg, t2: Reg, n: Reg, imm: i64) -> u32 {
    assert!(imm % 8 == 0);
    0xA980_0000 | simm(imm / 8, 7) << 15 | r(t2) << 10 | r(n) << 5 | r(t)
}
/// `ldp xt, xt2, [xn], #imm`.
pub fn ldp_post(t: Reg, t2: Reg, n: Reg, imm: i64) -> u32 {
    assert!(imm % 8 == 0);
    0xA8C0_0000 | simm(imm / 8, 7) << 15 | r(t2) << 10 | r(n) << 5 | r(t)
}
/// `stp xt, xt2, [xn, #imm]`.
pub fn stp(t: Reg, t2: Reg, n: Reg, imm: i64) -> u32 {
    assert!(imm % 8 == 0);
    0xA900_0000 | simm(imm / 8, 7) << 15 | r(t2) << 10 | r(n) << 5 | r(t)
}
/// `ldp xt, xt2, [xn, #imm]`.
pub fn ldp(t: Reg, t2: Reg, n: Reg, imm: i64) -> u32 {
    assert!(imm % 8 == 0);
    0xA940_0000 | simm(imm / 8, 7) << 15 | r(t2) << 10 | r(n) << 5 | r(t)
}

// --------------------------------------------------------------- arithmetic

/// `add xd, xn, #imm` (0..4096).
pub fn add_imm(d: Reg, n: Reg, imm: u32) -> u32 {
    assert!(imm < 4096);
    0x9100_0000 | imm << 10 | r(n) << 5 | r(d)
}
/// `sub xd, xn, #imm` (0..4096).
pub fn sub_imm(d: Reg, n: Reg, imm: u32) -> u32 {
    assert!(imm < 4096);
    0xD100_0000 | imm << 10 | r(n) << 5 | r(d)
}
/// `add xd, xn, xm`.
pub fn add(d: Reg, n: Reg, m: Reg) -> u32 {
    0x8B00_0000 | r(m) << 16 | r(n) << 5 | r(d)
}
/// `sub xd, xn, xm`.
pub fn sub(d: Reg, n: Reg, m: Reg) -> u32 {
    0xCB00_0000 | r(m) << 16 | r(n) << 5 | r(d)
}
/// `cmp xn, #imm` (0..4096).
pub fn cmp_imm(n: Reg, imm: u32) -> u32 {
    assert!(imm < 4096);
    0xF100_001F | imm << 10 | r(n) << 5
}
/// `cmp xn, xm`.
pub fn cmp(n: Reg, m: Reg) -> u32 {
    0xEB00_001F | r(m) << 16 | r(n) << 5
}
/// `csel xd, xn, xm, cond`.
pub fn csel(d: Reg, n: Reg, m: Reg, c: Cond) -> u32 {
    0x9A80_0000 | r(m) << 16 | (c as u32) << 12 | r(n) << 5 | r(d)
}
/// `mov xd, xm` (`orr xd, xzr, xm`).
pub fn mov(d: Reg, m: Reg) -> u32 {
    0xAA00_03E0 | r(m) << 16 | r(d)
}
/// `movz xd, #imm16, lsl #(16 * hw)`.
pub fn movz(d: Reg, imm16: u32, hw: u32) -> u32 {
    assert!(imm16 < 1 << 16 && hw < 4);
    0xD280_0000 | hw << 21 | imm16 << 5 | r(d)
}
/// `movk xd, #imm16, lsl #(16 * hw)`.
pub fn movk(d: Reg, imm16: u32, hw: u32) -> u32 {
    assert!(imm16 < 1 << 16 && hw < 4);
    0xF280_0000 | hw << 21 | imm16 << 5 | r(d)
}
/// Load any 64-bit constant: `movz` then as many `movk`s as needed.
pub fn mov_imm64(d: Reg, v: u64) -> Vec<u32> {
    let mut out = vec![movz(d, (v & 0xffff) as u32, 0)];
    for hw in 1..4 {
        let part = ((v >> (16 * hw)) & 0xffff) as u32;
        if part != 0 {
            out.push(movk(d, part, hw));
        }
    }
    out
}

// ------------------------------------------------------------------ control

/// `b` by `words` instructions (signed, 26 bits).
pub fn b(words: i64) -> u32 {
    0x1400_0000 | simm(words, 26)
}
/// `bl` by `words` instructions.
pub fn bl(words: i64) -> u32 {
    0x9400_0000 | simm(words, 26)
}
/// `b.cond` by `words` instructions (signed, 19 bits).
pub fn b_cond(c: Cond, words: i64) -> u32 {
    0x5400_0000 | simm(words, 19) << 5 | c as u32
}
/// `cbz xt` by `words` instructions.
pub fn cbz(t: Reg, words: i64) -> u32 {
    0xB400_0000 | simm(words, 19) << 5 | r(t)
}
/// `br xn`.
pub fn br(n: Reg) -> u32 {
    0xD61F_0000 | r(n) << 5
}
/// `blr xn`.
pub fn blr(n: Reg) -> u32 {
    0xD63F_0000 | r(n) << 5
}
/// `ret`.
pub fn ret() -> u32 {
    0xD65F_03C0
}

/// Instructions as the bytes that go in memory: little-endian words.
pub fn bytes(code: &[u32]) -> Vec<u8> {
    code.iter().flat_map(|w| w.to_le_bytes()).collect()
}
