//! Instructions shown: the inverse of `arm64`'s encoders, for the forms
//! they make, and nothing more. What falls outside them is shown as
//! `.word`, which no code this crate makes should contain
//! (`tests/arm64_disasm.rs` checks every instruction the machines make).

/// Instruction `w`, the `at`th of its code, as text. A branch's target is
/// shown as `@n`, the instruction it goes to, counted from the same start.
pub fn disassemble(w: u32, at: i64) -> String {
    let (d, n, m) = (w & 31, (w >> 5) & 31, (w >> 16) & 31);
    let t2 = (w >> 10) & 31;
    let imm9 = sext((w >> 12) & 0x1ff, 9);
    let imm7 = sext((w >> 15) & 0x7f, 7) * 8;
    let imm12 = (w >> 10) & 0xfff;
    let imm19 = sext((w >> 5) & 0x7_ffff, 19);
    let shift = (w >> 10) & 63;
    let (x, sp) = (xr, spr);
    let is = |mask: u32, val: u32| w & mask == val;
    let three = |op: &str| {
        if shift == 0 { format!("{op} {}, {}, {}", x(d), x(n), x(m)) } else { format!("{op} {}, {}, {}, lsl #{shift}", x(d), x(n), x(m)) }
    };
    match () {
        _ if w == 0xD503_201F => "nop".into(),
        _ if w == 0xD65F_03C0 => "ret".into(),
        _ if is(0xFFE0_0C00, 0xF840_0400) => format!("ldr {}, [{}], #{imm9}", x(d), sp(n)),
        _ if is(0xFFE0_0C00, 0xF840_0C00) => format!("ldr {}, [{}, #{imm9}]!", x(d), sp(n)),
        _ if is(0xFFE0_0C00, 0xF800_0400) => format!("str {}, [{}], #{imm9}", x(d), sp(n)),
        _ if is(0xFFE0_0C00, 0xF800_0C00) => format!("str {}, [{}, #{imm9}]!", x(d), sp(n)),
        _ if is(0xFFE0_0C00, 0xF840_0000) => format!("ldur {}, [{}, #{imm9}]", x(d), sp(n)),
        _ if is(0xFFE0_0C00, 0xB840_0000) => format!("ldur w{d}, [{}, #{imm9}]", sp(n)),
        _ if is(0xFFE0_0C00, 0xF800_0000) => format!("stur {}, [{}, #{imm9}]", x(d), sp(n)),
        _ if is(0xFFC0_0000, 0xF940_0000) => format!("ldr {}, [{}, #{}]", x(d), sp(n), imm12 * 8),
        _ if is(0xFFC0_0000, 0xF900_0000) => format!("str {}, [{}, #{}]", x(d), sp(n), imm12 * 8),
        _ if is(0xFFC0_0000, 0x3900_0000) => format!("strb w{d}, [{}, #{imm12}]", sp(n)),
        _ if is(0xFF00_0000, 0x5800_0000) => format!("ldr {}, {}", x(d), target(at, imm19)),
        _ if is(0xFFE0_FC00, 0xF860_6800) => format!("ldr {}, [{}, {}]", x(d), sp(n), x(m)),
        _ if is(0xFFC0_0000, 0xA980_0000) => format!("stp {}, {}, [{}, #{imm7}]!", x(d), x(t2), sp(n)),
        _ if is(0xFFC0_0000, 0xA8C0_0000) => format!("ldp {}, {}, [{}], #{imm7}", x(d), x(t2), sp(n)),
        _ if is(0xFFC0_0000, 0xA900_0000) => format!("stp {}, {}, [{}, #{imm7}]", x(d), x(t2), sp(n)),
        _ if is(0xFFC0_0000, 0xA940_0000) => format!("ldp {}, {}, [{}, #{imm7}]", x(d), x(t2), sp(n)),
        _ if is(0xFFC0_0000, 0x9100_0000) => format!("add {}, {}, #{imm12}", sp(d), sp(n)),
        _ if is(0xFFC0_0000, 0xD100_0000) => format!("sub {}, {}, #{imm12}", sp(d), sp(n)),
        _ if is(0xFFC0_001F, 0xF100_001F) => format!("cmp {}, #{imm12}", sp(n)),
        _ if is(0xFFC0_0000, 0xF100_0000) => format!("subs {}, {}, #{imm12}", x(d), sp(n)),
        _ if is(0xFFC0_0000, 0xB100_0000) => format!("adds {}, {}, #{imm12}", x(d), sp(n)),
        _ if is(0xFF20_001F, 0xEB00_001F) && shift == 0 => format!("cmp {}, {}", x(n), x(m)),
        _ if is(0xFFE0_FFFF, 0xEB20_63FF) => format!("cmp sp, {}", x(m)),
        _ if is(0xFF20_0000, 0x8B00_0000) => three("add"),
        _ if is(0xFF20_0000, 0xCB00_0000) => three("sub"),
        _ if is(0xFF20_0000, 0xAB00_0000) => three("adds"),
        _ if is(0xFF20_0000, 0xEB00_0000) => three("subs"),
        _ if is(0xFF20_0000, 0xAA00_0000) && n == 31 && shift == 0 => format!("mov {}, {}", x(d), x(m)),
        _ if is(0xFF20_0000, 0xAA00_0000) => three("orr"),
        _ if is(0xFF20_0000, 0xCA00_0000) => three("eor"),
        _ if is(0xFFFF_001F, 0xF240_001F) => format!("tst {}, #{:#x}", x(n), low_mask(w)),
        _ if is(0xFFC0_0000, 0x9240_0000) => format!("and {}, {}, #{:#x}", x(d), x(n), run_mask(w)),
        _ if is(0xFFC0_FC00, 0x9340_FC00) => format!("asr {}, {}, #{m}", x(d), x(n), m = (w >> 16) & 63),
        _ if is(0xFFC0_0000, 0xD340_0000) => {
            let (lsb, top) = ((w >> 16) & 63, (w >> 10) & 63);
            if top == 63 { format!("lsr {}, {}, #{lsb}", x(d), x(n)) } else { format!("ubfx {}, {}, #{lsb}, #{}", x(d), x(n), top - lsb + 1) }
        }
        _ if is(0xFFE0_0C00, 0x9A80_0000) => format!("csel {}, {}, {}, {}", x(d), x(n), x(m), cond((w >> 12) & 15)),
        _ if is(0xFF80_0000, 0xD280_0000) => mov16("movz", w),
        _ if is(0xFF80_0000, 0xF280_0000) => mov16("movk", w),
        _ if is(0x9F00_0000, 0x1000_0000) => {
            let bytes = sext(((w >> 5) & 0x7ffff) << 2 | (w >> 29) & 3, 21);
            format!("adr {}, {}", x(d), target(at, bytes / 4))
        }
        _ if is(0xFC00_0000, 0x1400_0000) => format!("b {}", target(at, sext(w & 0x3ff_ffff, 26))),
        _ if is(0xFC00_0000, 0x9400_0000) => format!("bl {}", target(at, sext(w & 0x3ff_ffff, 26))),
        _ if is(0xFF00_0010, 0x5400_0000) => format!("b.{} {}", cond(w & 15), target(at, imm19)),
        _ if is(0xFF00_0000, 0xB400_0000) => format!("cbz {}, {}", x(d), target(at, imm19)),
        _ if is(0xFF00_0000, 0xB500_0000) => format!("cbnz {}, {}", x(d), target(at, imm19)),
        _ if is(0xFFFF_FC1F, 0xD61F_0000) => format!("br {}", x(n)),
        _ if is(0xFFFF_FC1F, 0xD63F_0000) => format!("blr {}", x(n)),
        _ if is(0xFFFF_FC1F, 0xD65F_0000) => format!("ret {}", x(n)),
        _ if is(0xFFE0_FC00, 0x9AC0_0C00) => format!("sdiv {}, {}, {}", x(d), x(n), x(m)),
        _ if is(0xFFE0_8000, 0x9B00_8000) => format!("msub {}, {}, {}, {}", x(d), x(n), x(m), x((w >> 10) & 31)),
        _ => format!(".word {w:#010x}"),
    }
}

fn sext(v: u32, bits: u32) -> i64 {
    let s = 64 - bits;
    ((v as i64) << s) >> s
}

/// Register `r` where 31 is the zero register.
fn xr(r: u32) -> String {
    if r == 31 { "xzr".into() } else { format!("x{r}") }
}

/// Register `r` where 31 is the stack pointer.
fn spr(r: u32) -> String {
    if r == 31 { "sp".into() } else { format!("x{r}") }
}

fn target(at: i64, words: i64) -> String {
    format!("@{}", at + words)
}

/// The immediate of `and_low` and `tst_low`: the low `imms + 1` bits.
fn low_mask(w: u32) -> u64 {
    let bits = ((w >> 10) & 63) + 1;
    if bits == 64 { u64::MAX } else { (1u64 << bits) - 1 }
}

/// The immediate of `and_bits` (and `and_low`): those low bits rotated
/// right by `immr`, a run of ones from bit `(64 - immr) % 64`.
fn run_mask(w: u32) -> u64 {
    low_mask(w).rotate_right((w >> 16) & 63)
}

fn mov16(op: &str, w: u32) -> String {
    let (hw, imm) = ((w >> 21) & 3, (w >> 5) & 0xffff);
    if hw == 0 { format!("{op} {}, #{imm:#x}", xr(w & 31)) } else { format!("{op} {}, #{imm:#x}, lsl #{}", xr(w & 31), 16 * hw) }
}

fn cond(c: u32) -> &'static str {
    ["eq", "ne", "hs", "lo", "mi", "pl", "vs", "vc", "hi", "ls", "ge", "lt", "gt", "le", "al", "nv"][c as usize]
}
