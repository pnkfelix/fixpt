//! An arm64 encoder: only the instructions the native core uses, each one a
//! function returning its 32-bit word. Registers are numbered 0–30; 31 is
//! `sp` or `xzr`, as the instruction takes it.
//!
//! Every encoding is checked against the system assembler in
//! `tests/arm64.rs`, one instruction at a time. So this is the stage-0 oracle
//! for an encoder written in FX-26 later, and it answers to `as` now.

pub type Reg = u32;

pub mod disasm;

pub const SP: Reg = 31;
pub const XZR: Reg = 31;

/// Condition codes, for `b.cond` and `csel`.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum Cond {
    Eq = 0,
    Ne = 1,
    /// Unsigned ≥.
    Hs = 2,
    /// Unsigned <.
    Lo = 3,
    /// Negative: after `fcmp`, less than (false when unordered).
    Mi = 4,
    Vs = 6,
    Vc = 7,
    /// Unsigned >.
    Hi = 8,
    /// Unsigned ≤.
    Ls = 9,
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
/// `ldur wt, [xn, #imm]`: 32 bits, zero-extended into `xt`.
pub fn ldur_w(t: Reg, n: Reg, imm: i64) -> u32 {
    0xB840_0000 | simm(imm, 9) << 12 | r(n) << 5 | r(t)
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
/// `add xd, xn, xm, lsl #s`.
pub fn add_lsl(d: Reg, n: Reg, m: Reg, s: u32) -> u32 {
    assert!(s < 64);
    0x8B00_0000 | r(m) << 16 | s << 10 | r(n) << 5 | r(d)
}
/// `sub xd, xn, xm`.
pub fn sub(d: Reg, n: Reg, m: Reg) -> u32 {
    0xCB00_0000 | r(m) << 16 | r(n) << 5 | r(d)
}
/// `adds xd, xn, xm`: add, setting the flags (`vs` on signed overflow).
pub fn adds(d: Reg, n: Reg, m: Reg) -> u32 {
    0xAB00_0000 | r(m) << 16 | r(n) << 5 | r(d)
}
/// `subs xd, xn, xm`.
pub fn subs(d: Reg, n: Reg, m: Reg) -> u32 {
    0xEB00_0000 | r(m) << 16 | r(n) << 5 | r(d)
}
/// `subs xd, xn, #imm` (0..4096).
pub fn subs_imm(d: Reg, n: Reg, imm: u32) -> u32 {
    assert!(imm < 4096);
    0xF100_0000 | imm << 10 | r(n) << 5 | r(d)
}
/// `cmp sp, xm`: the stack pointer against a register (the extended
/// register form, which alone takes `sp`).
pub fn cmp_sp(m: Reg) -> u32 {
    0xEB20_63FF | r(m) << 16
}
/// `adds xd, xn, #imm`.
pub fn adds_imm(d: Reg, n: Reg, imm: u32) -> u32 {
    assert!(imm < 4096);
    0xB100_0000 | imm << 10 | r(n) << 5 | r(d)
}
/// `orr xd, xn, xm`.
pub fn orr(d: Reg, n: Reg, m: Reg) -> u32 {
    0xAA00_0000 | r(m) << 16 | r(n) << 5 | r(d)
}
/// `and xd, xn, #(2^bits - 1)`: the low `bits` bits (1..64).
pub fn and_low(d: Reg, n: Reg, bits: u32) -> u32 {
    assert!((1..64).contains(&bits));
    0x9240_0000 | (bits - 1) << 10 | r(n) << 5 | r(d)
}
/// `tst xn, #(2^bits - 1)`: are the low `bits` bits all zero?
pub fn tst_low(n: Reg, bits: u32) -> u32 {
    assert!((1..64).contains(&bits));
    0xF240_001F | (bits - 1) << 10 | r(n) << 5
}
/// `ubfx xd, xn, #lsb, #width`: an unsigned bit field.
pub fn ubfx(d: Reg, n: Reg, lsb: u32, width: u32) -> u32 {
    assert!(lsb < 64 && width >= 1 && lsb + width <= 64);
    0xD340_0000 | lsb << 16 | (lsb + width - 1) << 10 | r(n) << 5 | r(d)
}
/// `asr xd, xn, #s`: shift right, keeping the sign.
pub fn asr_imm(d: Reg, n: Reg, s: u32) -> u32 {
    assert!(s < 64);
    0x9340_FC00 | s << 16 | r(n) << 5 | r(d)
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
/// `lsr xd, xn, #s`.
pub fn lsr_imm(d: Reg, n: Reg, s: u32) -> u32 {
    assert!(s < 64);
    0xD340_FC00 | s << 16 | r(n) << 5 | r(d)
}
/// `strb wt, [xn]`.
pub fn strb(t: Reg, n: Reg) -> u32 {
    0x3900_0000 | r(n) << 5 | r(t)
}
/// The write barrier after a value is stored at `[obj, #off]`
/// (`docs/research/generational-gc.md`): that word's card marked, in the
/// card table whose biased address (`Heap::card_table_address`) is at
/// `[state, #cards]`. `t1` and `t2` are the caller's to lose; `obj` may be
/// one of them.
pub fn card_mark(obj: Reg, off: i64, state: Reg, cards: u32, t1: Reg, t2: Reg) -> Vec<u32> {
    assert!(off.unsigned_abs() < 4096, "a field's offset in reach of one `add`");
    vec![
        if off < 0 { sub_imm(t1, obj, off.unsigned_abs() as u32) } else { add_imm(t1, obj, off as u32) },
        lsr_imm(t1, t1, 9),
        ldr(t2, state, cards),
        add(t2, t2, t1),
        movz(t1, 1, 0),
        strb(t1, t2),
    ]
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
/// `cbnz xt` by `words` instructions.
pub fn cbnz(t: Reg, words: i64) -> u32 {
    0xB500_0000 | simm(words, 19) << 5 | r(t)
}
/// `adr xd`: the address `words` instructions from here (signed, 19 bits
/// of words; the low two bits of the byte offset are always zero).
pub fn adr(d: Reg, words: i64) -> u32 {
    let bytes = simm(words * 4, 21);
    0x1000_0000 | (bytes & 3) << 29 | (bytes >> 2) << 5 | r(d)
}
/// `br xn`.
pub fn br(n: Reg) -> u32 {
    0xD61F_0000 | r(n) << 5
}
/// `blr xn`.
pub fn blr(n: Reg) -> u32 {
    0xD63F_0000 | r(n) << 5
}
/// `nop`.
pub const NOP: u32 = 0xD503_201F;

/// `sdiv xd, xn, xm`: `n / m`, rounded toward zero.
pub fn sdiv(d: Reg, n: Reg, m: Reg) -> u32 {
    0x9AC0_0C00 | r(m) << 16 | r(n) << 5 | r(d)
}
/// `msub xd, xn, xm, xa`: `a − n × m`.
pub fn msub(d: Reg, n: Reg, m: Reg, a: Reg) -> u32 {
    0x9B00_8000 | r(m) << 16 | r(a) << 10 | r(n) << 5 | r(d)
}
/// `eor xd, xn, xm`.
pub fn eor(d: Reg, n: Reg, m: Reg) -> u32 {
    0xCA00_0000 | r(m) << 16 | r(n) << 5 | r(d)
}

/// `udiv xd, xn, xm`: `n / m`, unsigned.
pub fn udiv(d: Reg, n: Reg, m: Reg) -> u32 {
    0x9AC0_0800 | r(m) << 16 | r(n) << 5 | r(d)
}
/// `mul xd, xn, xm`: the low 64 bits of `n × m`.
pub fn mul(d: Reg, n: Reg, m: Reg) -> u32 {
    0x9B00_7C00 | r(m) << 16 | r(n) << 5 | r(d)
}
/// `smulh xd, xn, xm`: the high 64 bits of the signed `n × m`.
pub fn smulh(d: Reg, n: Reg, m: Reg) -> u32 {
    0x9B40_7C00 | r(m) << 16 | r(n) << 5 | r(d)
}
/// `and xd, xn, xm`.
pub fn and(d: Reg, n: Reg, m: Reg) -> u32 {
    0x8A00_0000 | r(m) << 16 | r(n) << 5 | r(d)
}
/// `and xd, xn, #mask`, the mask `width` ones from bit `lsb` (a run that
/// does not wrap, and is not all 64).
pub fn and_bits(d: Reg, n: Reg, lsb: u32, width: u32) -> u32 {
    assert!(width >= 1 && lsb + width <= 64 && width < 64);
    0x9240_0000 | ((64 - lsb) % 64) << 16 | (width - 1) << 10 | r(n) << 5 | r(d)
}
/// `lsl xd, xn, #s`.
pub fn lsl_imm(d: Reg, n: Reg, s: u32) -> u32 {
    assert!(s < 64);
    0xD340_0000 | ((64 - s) % 64) << 16 | (63 - s) << 10 | r(n) << 5 | r(d)
}
/// `lslv xd, xn, xm`: shift left by `m` modulo 64.
pub fn lslv(d: Reg, n: Reg, m: Reg) -> u32 {
    0x9AC0_2000 | r(m) << 16 | r(n) << 5 | r(d)
}
/// `lsrv xd, xn, xm`.
pub fn lsrv(d: Reg, n: Reg, m: Reg) -> u32 {
    0x9AC0_2400 | r(m) << 16 | r(n) << 5 | r(d)
}
/// `asrv xd, xn, xm`.
pub fn asrv(d: Reg, n: Reg, m: Reg) -> u32 {
    0x9AC0_2800 | r(m) << 16 | r(n) << 5 | r(d)
}

// ------------------------------------------------------- floating point
// `d` registers are numbered as `x` ones; each takes a double.

/// `fmov dd, xn`: the bits, into a `d` register.
pub fn fmov_to_d(d: Reg, n: Reg) -> u32 {
    0x9E67_0000 | r(n) << 5 | r(d)
}
/// `fmov xd, dn`: the bits, out of a `d` register.
pub fn fmov_from_d(d: Reg, n: Reg) -> u32 {
    0x9E66_0000 | r(n) << 5 | r(d)
}
/// A double's two-operand operation, `op` one of `fadd`'s kin (bits 15..10).
fn fp2(op: u32, d: Reg, n: Reg, m: Reg) -> u32 {
    0x1E60_0800 | op << 12 | r(m) << 16 | r(n) << 5 | r(d)
}
/// `fadd dd, dn, dm`.
pub fn fadd(d: Reg, n: Reg, m: Reg) -> u32 {
    fp2(2, d, n, m)
}
/// `fsub dd, dn, dm`.
pub fn fsub(d: Reg, n: Reg, m: Reg) -> u32 {
    fp2(3, d, n, m)
}
/// `fmul dd, dn, dm`.
pub fn fmul(d: Reg, n: Reg, m: Reg) -> u32 {
    fp2(0, d, n, m)
}
/// `fdiv dd, dn, dm`.
pub fn fdiv(d: Reg, n: Reg, m: Reg) -> u32 {
    fp2(1, d, n, m)
}
/// A double's one-operand operation, `op` in bits 20..15.
fn fp1(op: u32, d: Reg, n: Reg) -> u32 {
    0x1E60_4000 | op << 15 | r(n) << 5 | r(d)
}
/// `fabs dd, dn`.
pub fn fabs(d: Reg, n: Reg) -> u32 {
    fp1(1, d, n)
}
/// `fneg dd, dn`.
pub fn fneg(d: Reg, n: Reg) -> u32 {
    fp1(2, d, n)
}
/// `fsqrt dd, dn`.
pub fn fsqrt(d: Reg, n: Reg) -> u32 {
    fp1(3, d, n)
}
/// `frintn dd, dn`: to the nearest, ties to even.
pub fn frintn(d: Reg, n: Reg) -> u32 {
    fp1(8, d, n)
}
/// `frintp dd, dn`: toward +∞.
pub fn frintp(d: Reg, n: Reg) -> u32 {
    fp1(9, d, n)
}
/// `frintm dd, dn`: toward −∞.
pub fn frintm(d: Reg, n: Reg) -> u32 {
    fp1(10, d, n)
}
/// `frintz dd, dn`: toward zero.
pub fn frintz(d: Reg, n: Reg) -> u32 {
    fp1(11, d, n)
}
/// `fcmp dn, dm`: unordered (a NaN) sets C and V, so `mi`, `ls`, `gt`, `ge`
/// and `eq` are all false then.
pub fn fcmp(n: Reg, m: Reg) -> u32 {
    0x1E60_2000 | r(m) << 16 | r(n) << 5
}
/// `scvtf dd, xn`: a signed integer, correctly rounded.
pub fn scvtf(d: Reg, n: Reg) -> u32 {
    0x9E62_0000 | r(n) << 5 | r(d)
}
/// `fcvtzs xd, dn`: toward zero, saturating.
pub fn fcvtzs(d: Reg, n: Reg) -> u32 {
    0x9E78_0000 | r(n) << 5 | r(d)
}

/// `ret`.
pub fn ret() -> u32 {
    0xD65F_03C0
}

/// Instructions as the bytes that go in memory: little-endian words.
pub fn bytes(code: &[u32]) -> Vec<u8> {
    code.iter().flat_map(|w| w.to_le_bytes()).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Encodings the system assembler gives (`as -arch arm64`), for the
    /// instructions the FX-26 encoder does not have, which its test covers.
    #[test]
    fn as_the_system_assembler_encodes_them() {
        assert_eq!(ldur_w(15, 14, 4), 0xb84041cf);
        assert_eq!(ldur_w(1, 2, -8), 0xb85f8041);
        assert_eq!(add_lsl(0, 16, 15, 8), 0x8b0f2200);
        assert_eq!(add_lsl(14, 11, 13, 2), 0x8b0d096e);
        assert_eq!(sdiv(0, 1, 2), 0x9ac20c20);
        assert_eq!(sdiv(13, 14, 15), 0x9acf0dcd);
        assert_eq!(msub(0, 1, 2, 3), 0x9b028c20);
        assert_eq!(msub(16, 13, 14, 15), 0x9b0ebdb0);
        assert_eq!(eor(0, 1, 2), 0xca020020);
        assert_eq!(eor(13, 14, 15), 0xca0f01cd);
        assert_eq!(udiv(0, 1, 2), 0x9ac20820);
        assert_eq!(udiv(13, 14, 15), 0x9acf09cd);
        assert_eq!(mul(0, 1, 2), 0x9b027c20);
        assert_eq!(mul(13, 14, 15), 0x9b0f7dcd);
        assert_eq!(smulh(0, 1, 2), 0x9b427c20);
        assert_eq!(smulh(13, 14, 15), 0x9b4f7dcd);
        assert_eq!(and(0, 1, 2), 0x8a020020);
        assert_eq!(and(13, 14, 15), 0x8a0f01cd);
        assert_eq!(and_bits(0, 1, 3, 32), 0x927d7c20);
        assert_eq!(and_bits(13, 14, 3, 61), 0x927df1cd);
        assert_eq!(lsl_imm(0, 1, 29), 0xd3638820);
        assert_eq!(lsl_imm(13, 14, 3), 0xd37df1cd);
        assert_eq!(lslv(0, 1, 2), 0x9ac22020);
        assert_eq!(lsrv(13, 14, 15), 0x9acf25cd);
        assert_eq!(asrv(0, 1, 2), 0x9ac22820);
        assert_eq!(fmov_to_d(16, 1), 0x9e670030);
        assert_eq!(fmov_from_d(0, 16), 0x9e660200);
        assert_eq!(fadd(16, 16, 17), 0x1e712a10);
        assert_eq!(fsub(16, 16, 17), 0x1e713a10);
        assert_eq!(fmul(16, 16, 17), 0x1e710a10);
        assert_eq!(fdiv(16, 16, 17), 0x1e711a10);
        assert_eq!(fabs(16, 16), 0x1e60c210);
        assert_eq!(fneg(16, 16), 0x1e614210);
        assert_eq!(fsqrt(16, 16), 0x1e61c210);
        assert_eq!(frintm(16, 16), 0x1e654210);
        assert_eq!(frintp(16, 16), 0x1e64c210);
        assert_eq!(frintz(16, 16), 0x1e65c210);
        assert_eq!(frintn(16, 16), 0x1e644210);
        assert_eq!(fcmp(16, 17), 0x1e712200);
        assert_eq!(scvtf(16, 13), 0x9e6201b0);
        assert_eq!(fcvtzs(13, 16), 0x9e78020d);
    }
}
