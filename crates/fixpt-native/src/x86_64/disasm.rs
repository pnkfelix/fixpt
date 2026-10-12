//! Instructions shown: the inverse of `x86_64`'s encoders, for the forms
//! they make, and nothing more, in the assembler's Intel syntax. What falls
//! outside them is shown as `.byte`, which no code this crate makes should
//! contain (`tests/x86_64.rs` checks every encoder reads back).

use super::{Alu, Cond, NAMES, Shift};

/// The instruction at byte `at` of `code`, as text, and its length. A
/// branch's target is shown as `@n`, the byte it goes to, counted from the
/// start of `code`.
pub fn disassemble(code: &[u8], at: usize) -> (String, usize) {
    match decode(&code[at..], at) {
        Some((text, n)) => (text, n),
        None => (format!(".byte {:#04x}", code[at]), 1),
    }
}

/// Every instruction of `code`, a line each: its offset, bytes and text.
pub fn listing(code: &[u8]) -> String {
    let mut out = String::new();
    let mut at = 0;
    while at < code.len() {
        let (text, n) = disassemble(code, at);
        let bytes: Vec<String> = code[at..at + n].iter().map(|b| format!("{b:02x}")).collect();
        out.push_str(&format!("  {at:>6}: {:<30} {text}\n", bytes.join(" ")));
        at += n;
    }
    out
}

struct Rex {
    w: bool,
    r: u8,
    x: u8,
    b: u8,
    present: bool,
}

fn decode(c: &[u8], at: usize) -> Option<(String, usize)> {
    let mut i = 0;
    let mut opsize16 = false;
    if c.first() == Some(&0x66) {
        opsize16 = true;
        i += 1;
    }
    let mut rex = Rex { w: false, r: 0, x: 0, b: 0, present: false };
    if let Some(&p) = c.get(i)
        && p & 0xF0 == 0x40
    {
        rex = Rex { w: p & 8 != 0, r: (p >> 2 & 1) << 3, x: (p >> 1 & 1) << 3, b: (p & 1) << 3, present: true };
        i += 1;
    }
    let r64 = |n: u8| NAMES[n as usize].to_string();
    let r32 = |n: u8| ["eax", "ecx", "edx", "ebx", "esp", "ebp", "esi", "edi"].get(n as usize).map_or(format!("{}d", NAMES[n as usize]), |s| s.to_string());
    let r8 = |n: u8| ["al", "cl", "dl", "bl", "spl", "bpl", "sil", "dil"].get(n as usize).map_or(format!("{}b", NAMES[n as usize]), |s| s.to_string());
    let op = *c.get(i)?;
    i += 1;
    let target = |rel: i64, end: usize| format!("@{}", at as i64 + end as i64 + rel);
    let i32_at = |k: usize| -> Option<i32> { Some(i32::from_le_bytes(c.get(k..k + 4)?.try_into().ok()?)) };
    // ModRM at `i`: the `reg` field, the operand (a register, or memory as
    // text), and the bytes it took.
    let modrm = |i: usize, size: &str| -> Option<(u8, Operand, usize)> {
        let b = *c.get(i)?;
        let (md, reg, rm) = (b >> 6, (b >> 3 & 7) | rex.r, b & 7);
        if md == 3 {
            return Some((reg, Operand::Reg(rm | rex.b), 1));
        }
        let mut n = 1;
        let (base, index) = if rm == 4 {
            let sib = *c.get(i + 1)?;
            n += 1;
            let (scale, ix, base) = (1u8 << (sib >> 6), (sib >> 3 & 7) | rex.x, (sib & 7) | rex.b);
            (base, (ix != 4).then_some((ix, scale)))
        } else {
            (rm | rex.b, None)
        };
        if md == 0 && base & 7 == 5 {
            return None;
        }
        let disp = match md {
            1 => {
                n += 1;
                *c.get(i + n - 1)? as i8 as i32
            }
            2 => {
                n += 4;
                i32::from_le_bytes(c.get(i + n - 4..i + n)?.try_into().ok()?)
            }
            _ => 0,
        };
        let mut s = format!("{size}[{}", NAMES[base as usize]);
        if let Some((ix, scale)) = index {
            s += &format!("+{}", NAMES[ix as usize]);
            if scale != 1 {
                s += &format!("*{scale}");
            }
        }
        if disp != 0 {
            s += &if disp < 0 { format!("-{}", disp.unsigned_abs()) } else { format!("+{disp}") };
        }
        s.push(']');
        Some((reg, Operand::Mem(s), n))
    };
    let show = |o: &Operand, name: &dyn Fn(u8) -> String| match o {
        Operand::Reg(r) => name(*r),
        Operand::Mem(s) => s.clone(),
    };
    let w = rex.w;
    let text = match op {
        0x90 if !rex.present => (if opsize16 { "xchg ax, ax" } else { "nop" }.to_string(), i),
        0x0F => {
            let op2 = *c.get(i)?;
            i += 1;
            match op2 {
                0x1F => {
                    let (_, o, n) = modrm(i, "")?;
                    let _ = o;
                    ("nop".to_string(), i + n)
                }
                0x0B => ("ud2".to_string(), i),
                0x80..=0x8F => {
                    let rel = i32_at(i)? as i64;
                    (format!("j{} {}", Cond::from_bits(op2).name(), target(rel, i + 4)), i + 4)
                }
                0x40..=0x4F if w => {
                    let (reg, o, n) = modrm(i, "")?;
                    (format!("cmov{} {}, {}", Cond::from_bits(op2).name(), r64(reg), show(&o, &r64)), i + n)
                }
                0x90..=0x9F => {
                    let (_, o, n) = modrm(i, "")?;
                    (format!("set{} {}", Cond::from_bits(op2).name(), show(&o, &r8)), i + n)
                }
                0xAF if w => {
                    let (reg, o, n) = modrm(i, "")?;
                    (format!("imul {}, {}", r64(reg), show(&o, &r64)), i + n)
                }
                0xB6 if !w => {
                    let (reg, o, n) = modrm(i, "byte ptr ")?;
                    (format!("movzx {}, {}", r32(reg), show(&o, &r8)), i + n)
                }
                _ => return None,
            }
        }
        // The arithmetic group, register forms: `op r/m, r` and `op r, r/m`.
        0x01 | 0x09 | 0x11 | 0x19 | 0x21 | 0x29 | 0x31 | 0x39 | 0x03 | 0x0B | 0x13 | 0x1B | 0x23 | 0x2B | 0x33 | 0x3B if w => {
            let alu = alu_of(op >> 3).name();
            let (reg, o, n) = modrm(i, "")?;
            if op & 2 == 0 {
                (format!("{alu} {}, {}", show(&o, &r64), r64(reg)), i + n)
            } else {
                (format!("{alu} {}, {}", r64(reg), show(&o, &r64)), i + n)
            }
        }
        0x81 | 0x83 if w => {
            let (reg, o, n) = modrm(i, "qword ptr ")?;
            let (imm, k) = if op == 0x83 { (*c.get(i + n)? as i8 as i32, 1) } else { (i32_at(i + n)?, 4) };
            (format!("{} {}, {}", alu_of(reg & 7).name(), show(&o, &r64), imm), i + n + k)
        }
        0x85 if w => {
            let (reg, o, n) = modrm(i, "")?;
            (format!("test {}, {}", show(&o, &r64), r64(reg)), i + n)
        }
        0x89 => {
            let (reg, o, n) = modrm(i, "")?;
            if w { (format!("mov {}, {}", show(&o, &r64), r64(reg)), i + n) } else { (format!("mov {}, {}", show(&o, &r32), r32(reg)), i + n) }
        }
        0x8B => {
            let (reg, o, n) = modrm(i, "")?;
            if w { (format!("mov {}, {}", r64(reg), show(&o, &r64)), i + n) } else { (format!("mov {}, {}", r32(reg), show(&o, &r32)), i + n) }
        }
        0x63 if w => {
            let (reg, o, n) = modrm(i, "dword ptr ")?;
            (format!("movsxd {}, {}", r64(reg), show(&o, &r32)), i + n)
        }
        0x8D if w => {
            let (reg, o, n) = modrm(i, "")?;
            (format!("lea {}, {}", r64(reg), show(&o, &r64)), i + n)
        }
        0x99 if w => ("cqo".to_string(), i),
        0x05 | 0x0D | 0x15 | 0x1D | 0x25 | 0x2D | 0x35 | 0x3D if w => (format!("{} rax, {}", alu_of(op >> 3).name(), i32_at(i)?), i + 4),
        0xA9 if !w => (format!("test eax, {}", i32_at(i)? as u32), i + 4),
        0xB8..=0xBF => {
            let d = (op & 7) | rex.b;
            if w {
                let v = u64::from_le_bytes(c.get(i..i + 8)?.try_into().ok()?);
                (format!("movabs {}, {v:#x}", r64(d)), i + 8)
            } else {
                (format!("mov {}, {:#x}", r32(d), i32_at(i)? as u32), i + 4)
            }
        }
        0xC1 | 0xD1 | 0xD3 if w => {
            let (reg, o, n) = modrm(i, "")?;
            let name = [(4, Shift::Shl), (5, Shift::Shr), (7, Shift::Sar)].iter().find(|(d, _)| *d == reg & 7)?.1.name();
            match op {
                0xC1 => (format!("{name} {}, {}", show(&o, &r64), c.get(i + n)?), i + n + 1),
                0xD1 => (format!("{name} {}, 1", show(&o, &r64)), i + n),
                _ => (format!("{name} {}, cl", show(&o, &r64)), i + n),
            }
        }
        0xC3 => ("ret".to_string(), i),
        0xC6 if !w => {
            let (_, o, n) = modrm(i, "byte ptr ")?;
            (format!("mov {}, {}", show(&o, &r8), c.get(i + n)?), i + n + 1)
        }
        0xC7 if w => {
            let (_, o, n) = modrm(i, "qword ptr ")?;
            let imm = i32_at(i + n)?;
            match o {
                Operand::Reg(r) => (format!("mov {}, {imm}", r64(r)), i + n + 4),
                Operand::Mem(s) => (format!("mov {s}, {imm}"), i + n + 4),
            }
        }
        0xCC => ("int3".to_string(), i),
        0xE8 => (format!("call {}", target(i32_at(i)? as i64, i + 4)), i + 4),
        0xE9 => (format!("jmp {}", target(i32_at(i)? as i64, i + 4)), i + 4),
        0xEB => (format!("jmp {}", target(*c.get(i)? as i8 as i64, i + 1)), i + 1),
        0x70..=0x7F => (format!("j{} {}", Cond::from_bits(op).name(), target(*c.get(i)? as i8 as i64, i + 1)), i + 1),
        0x50..=0x57 if !w => (format!("push {}", r64((op & 7) | rex.b)), i),
        0x58..=0x5F if !w => (format!("pop {}", r64((op & 7) | rex.b)), i),
        0xF7 => {
            let (reg, o, n) = modrm(i, if w { "qword ptr " } else { "" })?;
            match (reg & 7, w) {
                (0, false) => (format!("test {}, {}", show(&o, &r32), i32_at(i + n)? as u32), i + n + 4),
                (2, true) => (format!("not {}", show(&o, &r64)), i + n),
                (3, true) => (format!("neg {}", show(&o, &r64)), i + n),
                (7, true) => (format!("idiv {}", show(&o, &r64)), i + n),
                _ => return None,
            }
        }
        0xFF if !w => {
            let (reg, o, n) = modrm(i, "qword ptr ")?;
            let name = match reg & 7 {
                2 => "call",
                4 => "jmp",
                6 => "push",
                _ => return None,
            };
            (format!("{name} {}", show(&o, &r64)), i + n)
        }
        0x8F if !w => {
            let (reg, o, n) = modrm(i, "qword ptr ")?;
            if reg & 7 != 0 {
                return None;
            }
            (format!("pop {}", show(&o, &r64)), i + n)
        }
        _ => return None,
    };
    Some(text)
}

enum Operand {
    Reg(u8),
    Mem(String),
}

fn alu_of(n: u8) -> Alu {
    [Alu::Add, Alu::Or, Alu::Adc, Alu::Sbb, Alu::And, Alu::Sub, Alu::Xor, Alu::Cmp][(n & 7) as usize]
}
