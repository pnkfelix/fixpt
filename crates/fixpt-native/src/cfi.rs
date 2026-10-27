//! How to unwind the machine code we make, for a debugger (`jitdebug`):
//! each instruction's rules, as DWARF call frame information, found from
//! the code itself rather than from the compiler that made it, so that the
//! Rust and the FX-26 compilers' code and the hand-written stubs are told
//! alike.
//!
//! x86_64 only, and only code entered by a `call` (or a tail call's `jmp`),
//! the return address on the stack's top: the native convention's
//! procedures, stubs and trampoline. From there each instruction is read
//! (`x86_64::disasm`), following branches, keeping where the frame's base
//! (the stack's top before the call, DWARF's CFA) is from `rsp` or `rbp`,
//! where the return address is, and where the caller's `rbp` is. Anything
//! that moves `rsp` or `rbp` in a way this does not know leaves the base
//! unknown, said so (the return address undefined), and a debugger stops
//! there rather than going on wrong.

use crate::x86_64::disasm::disassemble;

/// Where something the caller needs is: in its own place (`rbp` not yet
/// changed), at the base minus a number of bytes, in a register (by its
/// DWARF number), or lost.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum At {
    Same,
    Below(i32),
    Reg(u8),
    Lost,
}

/// What is known where an instruction starts: the base minus `rsp`, and
/// minus `rbp`, if known; the return address; the caller's `rbp`; and
/// where in the machine's state (`[r15+d]`) `rsp` and `rbp` were kept, and
/// what they were, as a call out to Rust keeps them while it runs on
/// Rust's stack, to have them back after.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
struct State {
    rsp: Option<i32>,
    rbp: Option<i32>,
    ra: At,
    fp: At,
    kept_rsp: Option<(i32, i32)>,
    kept_rbp: Option<(i32, i32)>,
}

/// As a call leaves it.
const ENTRY: State = State { rsp: Some(8), rbp: None, ra: At::Below(8), fp: At::Same, kept_rsp: None, kept_rbp: None };

/// DWARF's numbers for x86_64's registers, by name.
fn dwarf(name: &str) -> Option<u8> {
    let hw = crate::x86_64::NAMES.iter().position(|&n| n == name)?;
    Some(DWARF[hw])
}

/// DWARF's number for each register, by the hardware's.
const DWARF: [u8; 16] = [0, 2, 1, 3, 7, 6, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15];
const SP: u8 = 7;
const FP: u8 = 6;
const STATE: u8 = 15;

/// An operand, as far as frames care: a register (by its DWARF number);
/// memory at a register plus a displacement (`None` for any other address);
/// an immediate; or anything else (an `xmm` register).
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum Loc {
    Reg(u8),
    Mem(Option<u8>, i32),
    Imm(i32),
    Other,
}

/// What kind of instruction writes its first operand.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum Kind {
    Mov,
    Lea,
    Add,
    Sub,
    /// Writes nothing (`cmp`, `test`).
    None,
    Other,
}

/// An instruction, as far as frames care.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum Op {
    /// `ret`, `ud2`, `int3`: nothing after it.
    End,
    /// A jump, to an offset in the code if known.
    Jmp(Option<usize>),
    Jcc(Option<usize>),
    Call,
    Push(Loc),
    Pop(Loc),
    Ins(Kind, Loc, Loc),
}

/// The instruction at `at` in `code`, and its length; `None` where the
/// decoder does not know it (`x86_64::disasm` shows it as `.byte`). As
/// `disasm::decode`, case for case, without making text: what the frames
/// read of every piece of code made.
fn decode(c: &[u8], at: usize) -> Option<(Op, usize)> {
    let mut i = 0;
    let (mut opsize16, mut rep) = (false, 0u8);
    match c.get(at)? {
        0x66 => {
            opsize16 = true;
            i += 1;
        }
        &p @ (0xF2 | 0xF3) => {
            rep = p;
            i += 1;
        }
        _ => {}
    }
    let (mut w, mut rr, mut rx, mut rb, mut rex) = (false, 0u8, 0u8, 0u8, false);
    if let Some(&p) = c.get(at + i)
        && p & 0xF0 == 0x40
    {
        (w, rr, rx, rb, rex) = (p & 8 != 0, (p >> 2 & 1) << 3, (p >> 1 & 1) << 3, (p & 1) << 3, true);
        i += 1;
    }
    let _ = rx;
    let byte = |k: usize| c.get(at + k).copied();
    let i32_at = |k: usize| -> Option<i32> { i32::from_le_bytes(c.get(at + k..at + k + 4)?.try_into().ok()?).into() };
    let op = byte(i)?;
    i += 1;
    let reg = |n: u8| Loc::Reg(DWARF[n as usize & 15]);
    // ModRM at `i`: its `reg` field, the operand, and the bytes it took.
    let modrm = |i: usize| -> Option<(u8, Loc, usize)> {
        let b = byte(i)?;
        let (md, r, rm) = (b >> 6, (b >> 3 & 7) | rr, b & 7);
        if md == 3 {
            return Some((r, reg(rm | rb), 1));
        }
        if md == 0 && rm == 5 {
            i32_at(i + 1)?;
            return Some((r, Loc::Mem(None, 0), 5));
        }
        let mut n = 1;
        let (base, indexed) = if rm == 4 {
            let sib = byte(i + 1)?;
            n += 1;
            ((sib & 7) | rb, (sib >> 3 & 7) | rx != 4)
        } else {
            (rm | rb, false)
        };
        if md == 0 && base & 7 == 5 {
            return None;
        }
        let disp = match md {
            1 => {
                n += 1;
                byte(i + n - 1)? as i8 as i32
            }
            2 => {
                n += 4;
                i32_at(i + n - 4)?
            }
            _ => 0,
        };
        Some((r, if indexed { Loc::Mem(None, 0) } else { Loc::Mem(Some(DWARF[base as usize]), disp) }, n))
    };
    let target = |rel: i32, end: usize| usize::try_from(at as i64 + end as i64 + rel as i64).ok();
    let ins = |k: Kind, d: Loc, s: Loc| Op::Ins(k, d, s);
    Some(match op {
        0x90 if !rex => (ins(Kind::None, Loc::Other, Loc::Other), i),
        0x0F => {
            let op2 = byte(i)?;
            i += 1;
            match op2 {
                0x1F => {
                    let (_, _, n) = modrm(i)?;
                    (ins(Kind::None, Loc::Other, Loc::Other), i + n)
                }
                0x0B => (Op::End, i),
                0x80..=0x8F => (Op::Jcc(target(i32_at(i)?, i + 4)), i + 4),
                0x40..=0x4F | 0xAF if w => {
                    let (r, o, n) = modrm(i)?;
                    (ins(Kind::Other, reg(r), o), i + n)
                }
                0x90..=0x9F => {
                    let (_, o, n) = modrm(i)?;
                    (ins(Kind::Other, o, Loc::Other), i + n)
                }
                0xB6 | 0xB7 if !w => {
                    let (r, o, n) = modrm(i)?;
                    (ins(Kind::Other, reg(r), o), i + n)
                }
                0x6E | 0x7E if opsize16 => {
                    let (_, o, n) = modrm(i)?;
                    (if op2 == 0x6E { ins(Kind::Other, Loc::Other, o) } else { ins(Kind::Other, o, Loc::Other) }, i + n)
                }
                0x51 | 0x58 | 0x59 | 0x5C | 0x5E if rep != 0 => {
                    let (_, o, n) = modrm(i)?;
                    let Loc::Reg(_) = o else { return None };
                    (ins(Kind::Other, Loc::Other, Loc::Other), i + n)
                }
                0x2E => {
                    let (_, o, n) = modrm(i)?;
                    let Loc::Reg(_) = o else { return None };
                    (ins(Kind::None, Loc::Other, Loc::Other), i + n)
                }
                0x2A if rep == 0xF2 && w => {
                    let (_, o, n) = modrm(i)?;
                    (ins(Kind::Other, Loc::Other, o), i + n)
                }
                0x2C if rep == 0xF2 && w => {
                    let (r, o, n) = modrm(i)?;
                    let Loc::Reg(_) = o else { return None };
                    (ins(Kind::Other, reg(r), Loc::Other), i + n)
                }
                0x3A if opsize16 => {
                    let op3 = byte(i)?;
                    let (_, o, n) = modrm(i + 1)?;
                    let Loc::Reg(_) = o else { return None };
                    if !matches!(op3, 0x0A | 0x0B) {
                        return None;
                    }
                    byte(i + 1 + n)?;
                    (ins(Kind::Other, Loc::Other, Loc::Other), i + 2 + n)
                }
                _ => return None,
            }
        }
        0x01 | 0x09 | 0x11 | 0x19 | 0x21 | 0x29 | 0x31 | 0x39 | 0x03 | 0x0B | 0x13 | 0x1B | 0x23 | 0x2B | 0x33 | 0x3B if w => {
            let k = match op >> 3 {
                0 => Kind::Add,
                5 => Kind::Sub,
                7 => Kind::None,
                _ => Kind::Other,
            };
            let (r, o, n) = modrm(i)?;
            (if op & 2 == 0 { ins(k, o, reg(r)) } else { ins(k, reg(r), o) }, i + n)
        }
        0x81 | 0x83 if w => {
            let (r, o, n) = modrm(i)?;
            let (imm, k) = if op == 0x83 { (byte(i + n)? as i8 as i32, 1) } else { (i32_at(i + n)?, 4) };
            let kind = match r & 7 {
                0 => Kind::Add,
                5 => Kind::Sub,
                7 => Kind::None,
                _ => Kind::Other,
            };
            (ins(kind, o, Loc::Imm(imm)), i + n + k)
        }
        0x85 if w => {
            let (_, _, n) = modrm(i)?;
            (ins(Kind::None, Loc::Other, Loc::Other), i + n)
        }
        0x88 | 0x89 => {
            let (r, o, n) = modrm(i)?;
            // Only a whole register's store keeps it.
            (ins(Kind::Mov, o, if op == 0x89 && !opsize16 && w { reg(r) } else { Loc::Other }), i + n)
        }
        0x8B => {
            let (r, o, n) = modrm(i)?;
            (ins(if w { Kind::Mov } else { Kind::Other }, reg(r), o), i + n)
        }
        0x63 if w => {
            let (r, o, n) = modrm(i)?;
            (ins(Kind::Other, reg(r), o), i + n)
        }
        0x8D if w => {
            let (r, o, n) = modrm(i)?;
            (ins(Kind::Lea, reg(r), o), i + n)
        }
        0x99 if w => (ins(Kind::Other, reg(2), Loc::Other), i),
        0x05 | 0x0D | 0x15 | 0x1D | 0x25 | 0x2D | 0x35 | 0x3D if w => {
            i32_at(i)?;
            (ins(if op == 0x3D { Kind::None } else { Kind::Other }, reg(0), Loc::Other), i + 4)
        }
        0xA9 if !w => {
            i32_at(i)?;
            (ins(Kind::None, Loc::Other, Loc::Other), i + 4)
        }
        0xB8..=0xBF => {
            let d = (op & 7) | rb;
            if w {
                c.get(at + i..at + i + 8)?;
                (ins(Kind::Mov, reg(d), Loc::Other), i + 8)
            } else {
                (ins(Kind::Other, reg(d), Loc::Imm(i32_at(i)?)), i + 4)
            }
        }
        0xC1 | 0xD1 | 0xD3 if w => {
            let (r, o, n) = modrm(i)?;
            if ![4, 5, 7].contains(&(r & 7)) {
                return None;
            }
            if op == 0xC1 {
                byte(i + n)?;
            }
            (ins(Kind::Other, o, Loc::Other), i + n + (op == 0xC1) as usize)
        }
        0xC3 => (Op::End, i),
        0xC6 if !w => {
            let (_, o, n) = modrm(i)?;
            byte(i + n)?;
            (ins(Kind::Other, o, Loc::Other), i + n + 1)
        }
        0xC7 if w => {
            let (_, o, n) = modrm(i)?;
            (ins(Kind::Mov, o, Loc::Imm(i32_at(i + n)?)), i + n + 4)
        }
        0xCC => (Op::End, i),
        0xE8 => {
            i32_at(i)?;
            (Op::Call, i + 4)
        }
        0xE9 => (Op::Jmp(target(i32_at(i)?, i + 4)), i + 4),
        0xEB => (Op::Jmp(target(byte(i)? as i8 as i32, i + 1)), i + 1),
        0x70..=0x7F => (Op::Jcc(target(byte(i)? as i8 as i32, i + 1)), i + 1),
        0x50..=0x57 if !w => (Op::Push(reg((op & 7) | rb)), i),
        0x58..=0x5F if !w => (Op::Pop(reg((op & 7) | rb)), i),
        0xF7 => {
            let (r, o, n) = modrm(i)?;
            match (r & 7, w) {
                (0, false) => {
                    i32_at(i + n)?;
                    (ins(Kind::None, Loc::Other, Loc::Other), i + n + 4)
                }
                (2 | 3, true) => (ins(Kind::Other, o, Loc::Other), i + n),
                // `div`, `idiv`: `rax` and `rdx`.
                (6 | 7, true) => (ins(Kind::Other, reg(0), Loc::Other), i + n),
                _ => return None,
            }
        }
        0xFF if !w => {
            let (r, o, n) = modrm(i)?;
            match r & 7 {
                2 => (Op::Call, i + n),
                4 => (Op::Jmp(None), i + n),
                6 => (Op::Push(o), i + n),
                _ => return None,
            }
        }
        0x8F if !w => {
            let (r, o, n) = modrm(i)?;
            if r & 7 != 0 {
                return None;
            }
            (Op::Pop(o), i + n)
        }
        _ => return None,
    })
}

/// What one instruction does to the state, and where control goes after
/// it: on to the next, to an offset, or neither.
fn step(op: Op, s: State) -> (State, bool, Option<usize>) {
    let mut n = s;
    // Where memory at `l` is, from the base, if known.
    let below = |l: Loc| -> Option<i32> {
        match l {
            Loc::Mem(Some(SP), d) => s.rsp.map(|k| k - d),
            Loc::Mem(Some(FP), d) => s.rbp.map(|k| k - d),
            _ => None,
        }
    };
    let (kind, dest, src) = match op {
        Op::End => return (s, false, None),
        Op::Jmp(t) => return (s, false, t),
        Op::Jcc(t) => return (s, true, t),
        Op::Call => return (s, true, None),
        Op::Push(l) => {
            n.rsp = s.rsp.map(|k| k + 8);
            if let Some(k) = n.rsp {
                if l == Loc::Reg(FP) && s.fp == At::Same {
                    n.fp = At::Below(k);
                }
                if let At::Reg(r) = s.ra
                    && l == Loc::Reg(r)
                {
                    n.ra = At::Below(k);
                }
            }
            return (n, true, None);
        }
        Op::Pop(l) => {
            let from = s.rsp;
            n.rsp = s.rsp.map(|k| k - 8);
            let r = match l {
                Loc::Reg(r) => Some(r),
                _ => None,
            };
            if from.is_some() && s.ra == At::Below(from.unwrap_or(0)) {
                n.ra = r.map_or(At::Lost, At::Reg);
            } else if matches!(s.ra, At::Reg(x) if Some(x) == r) {
                n.ra = At::Lost;
            }
            if r == Some(FP) {
                n.rbp = None;
                if from.is_some() && s.fp == At::Below(from.unwrap_or(0)) {
                    n.fp = At::Same;
                } else if s.fp == At::Same {
                    n.fp = At::Lost;
                }
            }
            if r == Some(SP) {
                n.rsp = None;
            }
            return (n, true, None);
        }
        Op::Ins(k, d, s) => (k, d, s),
    };
    // A store: the return address, `rsp` or `rbp` kept where it goes.
    if let Loc::Mem(..) = dest {
        if kind == Kind::Mov {
            if let Loc::Mem(Some(STATE), d) = dest {
                if src == Loc::Reg(SP) {
                    n.kept_rsp = s.rsp.map(|v| (d, v));
                } else if src == Loc::Reg(FP) {
                    n.kept_rbp = s.rbp.map(|v| (d, v));
                }
            }
            if let Some(at) = below(dest) {
                if matches!(s.ra, At::Reg(r) if src == Loc::Reg(r)) {
                    n.ra = At::Below(at);
                }
                if src == Loc::Reg(FP) && s.fp == At::Same {
                    n.fp = At::Below(at);
                }
            }
        }
        return (n, true, None);
    }
    if kind == Kind::None {
        return (n, true, None);
    }
    let kept = |slot: Option<(i32, i32)>| match (src, slot) {
        (Loc::Mem(Some(STATE), d), Some((k, v))) if d == k => Some(v),
        _ => None,
    };
    match dest {
        Loc::Reg(SP) => {
            n.rsp = match (kind, src) {
                (Kind::Sub, Loc::Imm(k)) => s.rsp.map(|r| r + k),
                (Kind::Add, Loc::Imm(k)) => s.rsp.map(|r| r - k),
                (Kind::Lea, Loc::Mem(Some(SP), d)) => s.rsp.map(|r| r - d),
                (Kind::Lea, Loc::Mem(Some(FP), d)) => s.rbp.map(|r| r - d),
                (Kind::Mov, Loc::Reg(FP)) => s.rbp,
                (Kind::Mov, _) => kept(s.kept_rsp),
                _ => None,
            };
        }
        Loc::Reg(FP) => {
            n.rbp = match (kind, src) {
                (Kind::Lea, Loc::Mem(Some(SP), d)) => s.rsp.map(|r| r - d),
                (Kind::Mov, Loc::Reg(SP)) => s.rsp,
                (Kind::Mov, _) => kept(s.kept_rbp),
                _ => None,
            };
            if kind == Kind::Mov && below(src).is_some_and(|at| s.fp == At::Below(at)) {
                n.fp = At::Same;
            } else if s.fp == At::Same {
                n.fp = At::Lost;
            }
        }
        _ => {}
    }
    // A register written: the return address in it, read from where it
    // was kept, or lost.
    if let Loc::Reg(r) = dest {
        if kind == Kind::Mov && below(src).is_some_and(|at| s.ra == At::Below(at)) {
            n.ra = At::Reg(r);
        } else if s.ra == At::Reg(r) {
            n.ra = At::Lost;
        }
    }
    (n, true, None)
}

/// Each instruction's start in `code`, and its state, in order. An
/// instruction no path from the start reaches (another entry) starts as
/// a call leaves it. An instruction the decoder does not know is taken as
/// one byte that ends its path, as the disassembler shows it.
fn states(code: &[u8]) -> Vec<(usize, State)> {
    let mut starts = Vec::new();
    let mut ops = Vec::new();
    let mut at = 0;
    while at < code.len() {
        let (op, n) = decode(code, at).unwrap_or((Op::End, 1));
        starts.push(at);
        ops.push(op);
        at += n;
    }
    flow(&starts, &ops)
}

/// The states where each instruction of `ops`, at `starts`, starts: on
/// along straight code, each branch's target kept for later.
fn flow(starts: &[usize], ops: &[Op]) -> Vec<(usize, State)> {
    let index = |off: usize| starts.binary_search(&off).ok();
    let mut known: Vec<Option<State>> = vec![None; starts.len()];
    let mut work: Vec<usize> = Vec::new();
    for seed in 0..starts.len() {
        if known[seed].is_some() {
            continue;
        }
        known[seed] = Some(ENTRY);
        work.push(seed);
        while let Some(mut i) = work.pop() {
            let Some(mut s) = known[i] else { continue };
            loop {
                let (n, on, to) = step(ops[i], s);
                if let Some(t) = to.and_then(index)
                    && known[t].is_none()
                {
                    known[t] = Some(n);
                    work.push(t);
                }
                if !on || i + 1 >= starts.len() || known[i + 1].is_some() {
                    break;
                }
                i += 1;
                known[i] = Some(n);
                s = n;
            }
        }
    }
    starts.iter().copied().zip(known.into_iter().map(|k| k.unwrap_or(ENTRY))).collect()
}

/// The same states, the instructions read through the disassembler's
/// text: a check of [`decode`] (`FIXPT_CFI_CHECK`, and the tests).
fn states_by_text(code: &[u8]) -> Vec<(usize, State)> {
    let mut starts = Vec::new();
    let mut ops = Vec::new();
    let mut at = 0;
    while at < code.len() {
        let (text, n) = disassemble(code, at);
        starts.push(at);
        ops.push(op_of_text(&text));
        at += n;
    }
    flow(&starts, &ops)
}

/// An instruction, from the disassembler's text.
fn op_of_text(text: &str) -> Op {
    let (mn, rest) = text.split_once(' ').unwrap_or((text, ""));
    let ops: Vec<&str> = rest.split(", ").collect();
    let target = |o: &str| o.strip_prefix('@').and_then(|n| n.parse().ok());
    let loc = |o: &str| -> Loc {
        if o.contains('[') {
            let o = o.rsplit("ptr ").next().unwrap_or(o).trim_start_matches('[').trim_end_matches(']');
            let (b, d) = match (o.split_once('+'), o.split_once('-')) {
                (Some((b, d)), _) => (b, d.parse().ok()),
                (None, Some((b, d))) => (b, d.parse::<i32>().ok().map(|d| -d)),
                _ => (o, Some(0)),
            };
            return match (dwarf(b), d) {
                (Some(r), Some(d)) => Loc::Mem(Some(r), d),
                _ => Loc::Mem(None, 0),
            };
        }
        if let Ok(k) = o.parse() {
            return Loc::Imm(k);
        }
        dwarf(o).map_or(Loc::Other, Loc::Reg)
    };
    match mn {
        "ret" | "ud2" | "int3" | ".byte" => Op::End,
        "jmp" => Op::Jmp(target(ops[0])),
        "call" => Op::Call,
        _ if mn.starts_with('j') => Op::Jcc(target(ops[0])),
        "push" => Op::Push(loc(ops[0])),
        "pop" => Op::Pop(loc(ops[0])),
        _ => {
            let k = match mn {
                "mov" | "movabs" => Kind::Mov,
                "lea" => Kind::Lea,
                "add" => Kind::Add,
                "sub" => Kind::Sub,
                "cmp" | "test" | "ucomisd" | "ucomiss" | "nop" => Kind::None,
                _ => Kind::Other,
            };
            Op::Ins(k, loc(ops[0]), ops.get(1).map_or(Loc::Other, |o| loc(o)))
        }
    }
}

fn uleb(out: &mut Vec<u8>, mut v: u64) {
    loop {
        let b = (v & 0x7f) as u8;
        v >>= 7;
        if v == 0 {
            out.push(b);
            return;
        }
        out.push(b | 0x80);
    }
}

fn sleb(out: &mut Vec<u8>, mut v: i64) {
    loop {
        let b = (v & 0x7f) as u8;
        v >>= 7;
        if (v == 0 && b & 0x40 == 0) || (v == -1 && b & 0x40 != 0) {
            out.push(b);
            return;
        }
        out.push(b | 0x80);
    }
}

const RA: u8 = 16;

/// The rules for `s`, as DWARF CFA instructions, those that differ from
/// `was`'s.
fn rules(out: &mut Vec<u8>, s: State, was: Option<State>) {
    // The base: from `rsp`; else from where `rsp` was kept in the machine's
    // state (`r15` is kept by what is called); else from `rbp`.
    #[derive(PartialEq)]
    enum Cfa {
        Reg(u8, i32),
        Kept(i32, i32),
    }
    let cfa = |s: State| match (s.rsp, s.kept_rsp, s.rbp) {
        (Some(k), _, _) => Some(Cfa::Reg(7, k)),
        (None, Some((d, v)), _) => Some(Cfa::Kept(d, v)),
        (None, None, Some(k)) => Some(Cfa::Reg(FP, k)),
        _ => None,
    };
    let lost = cfa(s).is_none() || s.ra == At::Lost;
    if cfa(s) != was.and_then(cfa) {
        match cfa(s) {
            Some(Cfa::Reg(r, k)) => {
                out.push(0x0c); // DW_CFA_def_cfa
                uleb(out, r as u64);
                uleb(out, k as u64);
            }
            Some(Cfa::Kept(d, v)) => {
                let mut e = vec![0x7f]; // DW_OP_breg15
                sleb(&mut e, d as i64);
                e.push(0x06); // DW_OP_deref
                e.push(0x23); // DW_OP_plus_uconst
                uleb(&mut e, v as u64);
                out.push(0x0f); // DW_CFA_def_cfa_expression
                uleb(out, e.len() as u64);
                out.extend_from_slice(&e);
            }
            None => {}
        }
    }
    let put = |out: &mut Vec<u8>, reg: u8, at: At| match at {
        At::Same => {
            out.push(0x08); // DW_CFA_same_value
            uleb(out, reg as u64);
        }
        At::Below(k) => {
            out.push(0x80 | reg); // DW_CFA_offset, factored by -8
            uleb(out, (k / 8) as u64);
        }
        At::Reg(r) => {
            out.push(0x09); // DW_CFA_register
            uleb(out, reg as u64);
            uleb(out, r as u64);
        }
        At::Lost => {
            out.push(0x07); // DW_CFA_undefined
            uleb(out, reg as u64);
        }
    };
    let ra = if lost { At::Lost } else { s.ra };
    let was_ra = was.map(|w| if cfa(w).is_none() || w.ra == At::Lost { At::Lost } else { w.ra });
    if Some(ra) != was_ra {
        put(out, RA, ra);
    }
    if was.map(|w| w.fp) != Some(s.fp) {
        put(out, FP, s.fp);
    }
}

/// The CFA instructions for `code`, entered by a call, row by row; none
/// where this is not x86_64.
pub fn frame_of(code: &[u8]) -> Option<Vec<u8>> {
    if !cfg!(target_arch = "x86_64") {
        return None;
    }
    if std::env::var_os("FIXPT_CFI_DUMP").is_some() {
        for (at, st) in states(code) {
            eprintln!("  {at:>6}: {:<40} {st:?}", disassemble(code, at).0);
        }
    }
    if std::env::var_os("FIXPT_CFI_CHECK").is_some() {
        let (a, b) = (states(code), states_by_text(code));
        if a != b {
            let at = a.iter().zip(&b).position(|(x, y)| x != y).unwrap_or(a.len().min(b.len()));
            eprintln!("FIXPT_CFI_CHECK: the decoder and the text differ at instruction {at}:");
            for k in at.saturating_sub(3)..(at + 2).min(a.len()) {
                eprintln!("  {:>6}: {:<40} {:?}\n          {:?}", a[k].0, disassemble(code, a[k].0).0, a[k].1, b.get(k).map(|x| x.1));
            }
        }
    }
    let mut out = Vec::new();
    let mut was: Option<State> = Some(ENTRY);
    let mut last = 0;
    for (at, s) in states(code) {
        if Some(s) == was {
            continue;
        }
        let mut row = Vec::new();
        rules(&mut row, s, was);
        was = Some(s);
        if row.is_empty() {
            continue;
        }
        out.push(0x04); // DW_CFA_advance_loc4
        out.extend_from_slice(&((at - last) as u32).to_le_bytes());
        out.extend_from_slice(&row);
        last = at;
    }
    Some(out)
}

/// A `.debug_frame` of one CIE, whose rules are a call's, and an FDE for
/// each piece of code: its first address, its length in bytes, and its
/// further rules.
pub fn debug_frame(pieces: &[(u64, u64, &[u8])]) -> Vec<u8> {
    let mut cie = Vec::new();
    cie.extend_from_slice(&0xffff_ffffu32.to_le_bytes()); // a CIE
    cie.push(1); // version
    cie.push(0); // no augmentation
    uleb(&mut cie, 1); // code alignment
    cie.push(0x78); // data alignment, -8
    cie.push(RA);
    cie.extend_from_slice(&[0x0c, 7, 8]); // CFA rsp + 8
    cie.extend_from_slice(&[0x80 | RA, 1]); // return address at CFA - 8
    cie.extend_from_slice(&[0x08, FP]); // rbp the caller's
    let mut out = Vec::new();
    let put = |out: &mut Vec<u8>, mut body: Vec<u8>| {
        while !(body.len() + 4).is_multiple_of(8) {
            body.push(0); // DW_CFA_nop
        }
        out.extend_from_slice(&(body.len() as u32).to_le_bytes());
        out.extend_from_slice(&body);
    };
    put(&mut out, cie);
    for &(start, len, insns) in pieces {
        let mut fde = Vec::new();
        fde.extend_from_slice(&0u32.to_le_bytes()); // its CIE, at 0
        fde.extend_from_slice(&start.to_le_bytes());
        fde.extend_from_slice(&len.to_le_bytes());
        fde.extend_from_slice(insns);
        put(&mut out, fde);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::x86_64::*;

    /// A frame pushed as the native convention pushes one, and popped for
    /// a `ret`: the base found from `rsp` throughout, the return address
    /// on the stack, then in `r11`, then in the frame, and back.
    #[test]
    fn a_native_frame() {
        let mut c = Vec::new();
        for i in [pop(R11), sub_imm(RSP, 48), store(m(RSP, 8), RBP), store(m(RSP, 16), R11), lea(RBP, m(RSP, 8))] {
            c.extend_from_slice(&i);
        }
        let body = c.len();
        for i in [load(R11, m(RSP, 16)), load(RBP, m(RSP, 8)), add_imm(RSP, 40), store(m(RSP, 0), R11), ret()] {
            c.extend_from_slice(&i);
        }
        let s = states(&c);
        assert_eq!(s[0].1, ENTRY);
        assert_eq!(s[1].1, State { rsp: Some(0), ra: At::Reg(11), ..ENTRY });
        let framed = s.iter().find(|(at, _)| *at == body).unwrap().1;
        assert_eq!(framed, State { rsp: Some(48), rbp: Some(40), ra: At::Below(32), fp: At::Below(40), ..ENTRY });
        let last = s.last().unwrap().1;
        assert_eq!(last, ENTRY);
        assert_eq!(s, states_by_text(&c));
    }
}
