//! The assembler's pieces and the sequences of no procedure, by name, for
//! `fx_arm64::oracle` (`native-direct-arm64-asm.fx`), each run in an `Asm`
//! of its own (`harness`). Each piece's arguments are integers.

use super::super::*;

/// The traps' stubs, as `procedure` places them.
pub(super) fn place_stubs(a: &mut Asm, stubs: &[(Label, u32)]) {
    let kinds: Vec<Label> = (0..TRAPS.len()).map(|_| a.label()).collect();
    for (l, code) in stubs {
        a.bind(*l);
        a.to(kinds[*code as usize], Fix::Bl);
    }
    for (code, l) in kinds.iter().enumerate().skip(1) {
        if !stubs.iter().any(|(_, c)| *c as usize == code) {
            continue;
        }
        a.bind(*l);
        a.e(movz(X9, code as u32, 0));
        a.e(ldr(X16, ST, st_off(offset_of!(DState, trap_stub))));
        a.e(br(X16));
    }
}

/// A piece run in an `Asm` of its own: `piece` given it, its call-outs and
/// stubs, and the labels it makes for others to place (`outside`); then
/// those labels bound, in order, a `brk #0` after them, its traps' stubs
/// placed, and each call-out's load given field `n + 3`. Its bytes, after
/// `pre`, which a piece that answers something gives; and its call-outs
/// (`fx::callout_code`), numbered after the machine's own; or why not, as
/// a byte `0xee` and the message.
pub(super) fn harness(piece: impl FnOnce(&mut Asm, &mut Vec<Callout>, &mut Vec<(Label, u32)>, &mut Vec<Label>, &mut Vec<u8>)) -> (Vec<u8>, Vec<i64>) {
    let mut a = Asm::new();
    // The machine's own first, as a compile's are numbered after them.
    let mut callouts: Vec<Callout> = vec![Callout::Foreign; OWN_CALLOUTS];
    let mut stubs: Vec<(Label, u32)> = Vec::new();
    let mut outside: Vec<Label> = Vec::new();
    let mut pre: Vec<u8> = Vec::new();
    piece(&mut a, &mut callouts, &mut stubs, &mut outside, &mut pre);
    for l in outside {
        a.bind(l);
    }
    a.e(0xD420_0000);
    place_stubs(&mut a, &stubs);
    a.callout_fields(|n| n + 3);
    let calls = callouts[OWN_CALLOUTS..].iter().map(|&c| fx::callout_code(c)).collect();
    match a.finish() {
        Ok(code) => {
            pre.extend(crate::arm64::bytes(&code));
            (pre, calls)
        }
        Err(e) => {
            pre.push(0xee);
            pre.extend(e.bytes());
            (pre, calls)
        }
    }
}

pub(super) fn oracle(name: &str, args: &[i64]) -> Option<(Vec<u8>, Vec<i64>)> {
    let r = |k: usize| args[k] as Reg;
    Some(match name {
        "continuation-code" => (crate::arm64::bytes(&continuation_code(args[0] as usize)), Vec::new()),
        "push-frame" => harness(|a, _, _, _, _| push_frame(a, r(0), args[1] as u64)),
        "pop-frame" => harness(|a, _, _, _, _| pop_frame(a, args[0] as u64)),
        "leave" => harness(|a, _, _, _, _| leave(a)),
        "resume" => harness(|a, _, _, _, _| resume(a)),
        "call-out" => harness(|a, _, _, _, _| call_out(a, args[0] as usize)),
        // At `args[1]` instructions in, field `args[2]`.
        "ldr-field" => harness(|a, _, _, _, _| {
            for _ in 0..args[1] {
                a.e(NOP);
            }
            ldr_field(a, r(0), args[2] as usize);
        }),
        // A pure call of primitive `args[0]` on the registers after `into`.
        "pure-call" => harness(|a, callouts, _, _, _| {
            let regs: Vec<Reg> = args[2..].iter().map(|&x| x as Reg).collect();
            pure_call(a, callouts, Callout::Pure { p: args[0] as usize, n: regs.len() }, &regs, r(1));
        }),
        "check-fixnum" => harness(|a, _, _, outside, _| {
            let general = a.label();
            outside.push(general);
            check_fixnum(a, r(0), general);
        }),
        "card-mark" => harness(|a, _, _, _, _| a.es(&card_mark(r(0), args[1], ST, st_off(offset_of!(DState, cards)), r(2), r(3)))),
        // The 64 bits `hi` · 2^32 + `lo` into `r`.
        "imm" => harness(|a, _, _, _, _| a.es(&mov_imm64(r(0), ((args[1] as u64) << 32) | args[2] as u64))),
        // Traps of the codes given, each where `cond` (the next) holds.
        "traps" => harness(|a, _, stubs, _, _| {
            for c in args.chunks(2) {
                trap_at(a, stubs, c[0] as u32, cond_of(c[1]));
            }
        }),
        // Branches: `args[0]` labels made; then each `(kind, label, nops)`,
        // the branch and that many `nop`s after it; then the labels bound
        // in order, a `ret` after each odd one.
        "branches" => harness(|a, _, _, _, _| {
            let ls: Vec<Label> = (0..args[0]).map(|_| a.label()).collect();
            for f in args[1..].chunks(3) {
                a.to(ls[f[1] as usize], fix_of(f[0]));
                for _ in 0..f[2] {
                    a.e(NOP);
                }
            }
            for (k, l) in ls.iter().enumerate() {
                a.bind(*l);
                if k % 2 == 1 {
                    a.e(ret());
                }
            }
        }),
        // A label never placed.
        "unplaced" => harness(|a, _, _, _, _| {
            let l = a.label();
            a.to(l, Fix::B);
        }),
        _ => return None,
    })
}

/// A condition by its number.
pub(super) fn cond_of(c: i64) -> Cond {
    [Cond::Eq, Cond::Ne, Cond::Hs, Cond::Lo, Cond::Mi, Cond::Eq, Cond::Vs, Cond::Vc, Cond::Hi, Cond::Ls, Cond::Ge, Cond::Lt, Cond::Gt, Cond::Le][c as usize]
}

/// A branch's kind as `native-direct-arm64-asm.fx` numbers it.
pub(super) fn fix_of(f: i64) -> Fix {
    match f {
        16 => Fix::B,
        17 => Fix::Bl,
        32.. => Fix::Adr((f - 32) as Reg),
        c => Fix::If(cond_of(c)),
    }
}
