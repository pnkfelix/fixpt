//! The raw values' pieces of `direct.rs` by name (`fx_arm64::oracle`), for
//! `native-direct-arm64-raw.fx` to be checked against: `box_reg` to
//! `int_of_f64`, `f32_fast`, `f64_fast`, `raw_compare` to `wrap_small`, and
//! `IntSlow`, each run in an `Asm` of its own (`oracle_asm::harness`). Each
//! piece's arguments are integers: registers, flags (0 or 1), and a name
//! (`what`) as its bytes, last. A piece that answers something gives it
//! first (`pre`): a flag as a byte, a condition's number (0xff for none),
//! a skip as two bytes, lowest first.

use super::super::*;
use super::oracle_asm::harness;

/// The name at the end of `args`, from `k` on.
fn name_at(args: &[i64], k: usize) -> String {
    args[k..].iter().map(|&b| b as u8 as char).collect()
}

pub(super) fn oracle(name: &str, args: &[i64]) -> Option<(Vec<u8>, Vec<i64>)> {
    let r = |k: usize| args[k] as Reg;
    let flag = |k: usize| args[k] != 0;
    Some(match name {
        "box-reg" => harness(|a, callouts, _, _, _| box_reg(a, callouts, r(0), flag(1))),
        "unbox-reg" => harness(|a, callouts, _, _, _| unbox_reg(a, callouts, r(0))),
        "unbox-f64" => harness(|a, _, _, _, _| unbox_f64(a, r(0))),
        // The mark, as an instruction.
        "raw-f64-mark" => harness(|a, _, _, _, _| a.e(raw_f64_mark())),
        "take-raw-f64" => harness(|a, _, _, _, _| take_raw_f64(a)),
        "raw-return" => harness(|a, callouts, _, _, _| raw_return(a, callouts)),
        "raw-entry-skip" => harness(|_, _, _, _, pre| pre.extend((raw_entry_skip(args[0] as usize) as u16).to_le_bytes())),
        "box-f64" => harness(|a, callouts, _, _, _| box_f64(a, callouts, r(0))),
        "unbox-to" => harness(|a, callouts, _, _, _| unbox_to(a, callouts, r(0), rep_of(args[1]))),
        // `result`, then the conversions.
        "convert" => harness(|a, callouts, _, outside, _| {
            let general = a.label();
            outside.push(general);
            let cs: Vec<Convert> = args[1..].iter().map(|&c| convert_of(c)).collect();
            convert(a, callouts, &cs, general, r(0));
        }),
        "f64-of-int" => harness(|a, callouts, _, _, _| f64_of_int(a, callouts, args[0] as usize)),
        "int-of-f64" => harness(|a, callouts, stubs, _, _| int_of_f64(a, callouts, stubs, args[0] as usize)),
        "f64-fast" => harness(|a, _, _, _, _| f64_fast(a, &name_at(args, 1), r(0))),
        "f32-fast" => harness(|a, _, _, _, pre| pre.push(f32_fast(a, &name_at(args, 1), r(0)) as u8)),
        "compare" => harness(|_, _, _, _, pre| pre.push(raw_compare(flag(0), &name_at(args, 1)).map_or(0xff, |c| c as u8))),
        "raw-fast" => harness(|a, _, stubs, _, _| raw_fast(a, stubs, flag(0), &name_at(args, 2), r(1))),
        "wrap-small" => harness(|a, _, _, _, _| wrap_small(a, flag(0), args[1] as u32)),
        // Has an overflow, x, y (-1 with an immediate), the immediate, into,
        // the primitive, a difference, has a branch, taken when true: its
        // labels entry, overflow, back and branch, made in that order; back
        // and branch bound after it.
        "int-slow" => harness(|a, callouts, stubs, outside, _| {
            let entry = a.label();
            let overflow = flag(0).then(|| a.label());
            let back = a.label();
            let branch = flag(7).then(|| a.label());
            outside.push(back);
            outside.extend(branch);
            let s = IntSlow {
                entry,
                overflow,
                back,
                x: r(1),
                y: if args[2] < 0 { X16 } else { r(2) },
                imm: (args[2] < 0).then_some(args[3] as u32),
                into: r(4),
                prim: args[5] as usize,
                sub: flag(6),
                branch: branch.map(|l| (l, flag(8))),
            };
            s.emit(a, callouts, stubs);
        }),
        _ => return None,
    })
}

/// A representation, as `native-reps-sig` numbers it.
fn rep_of(n: i64) -> Rep {
    match n {
        0 => Rep::Undefined,
        1 => Rep::Value,
        2 => Rep::Raw { signed: true },
        3 => Rep::Raw { signed: false },
        4 => Rep::F64,
        _ => Rep::Fix,
    }
}

/// A conversion, as `native-reps-sig` numbers it: 128 · kind (box,
/// unbox, check) + 8 · register + representation.
fn convert_of(c: i64) -> Convert {
    let (r, rep) = (((c / 8) % 16) as usize, rep_of(c % 8));
    match c / 128 {
        0 => Convert::Box { r, rep },
        1 => Convert::Unbox { r, rep },
        _ => Convert::Check { r },
    }
}
