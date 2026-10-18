//! The Rust compiler's raw-value pieces by name, for `super::oracle`: the
//! pieces `native-direct-x64-raw.fx` ports (`box_reg` to `narrow_fast`, and
//! `IntSlow`), each run in an `Asm` of its own. Each piece's arguments are
//! integers: registers, flags (0 or 1), and a name (`what`) as its bytes,
//! last. The labels a piece is given are made before it and bound after it,
//! in order; then its traps' stubs are placed, as `procedure_x64` places
//! them. A piece that answers whether it did something gives that first,
//! as a byte (1 or 0), before its code.

use super::*;

/// The traps' stubs, as `procedure_x64` places them.
fn place_stubs(a: &mut Asm, stubs: &[(Label, u32)]) {
    let kinds: Vec<Label> = (0..TRAPS.len()).map(|_| a.label()).collect();
    for (l, code) in stubs {
        a.bind(*l);
        a.call_l(kinds[*code as usize]);
    }
    for (code, l) in kinds.iter().enumerate().skip(1) {
        if !stubs.iter().any(|(_, c)| *c as usize == code) {
            continue;
        }
        a.bind(*l);
        a.imm(X9, code as u64);
        a.e(jmp_m(st(offset_of!(DState, trap_stub))));
    }
}

/// The name at the end of `args`, from `k` on.
fn name_at(args: &[i64], k: usize) -> String {
    args[k..].iter().map(|&b| b as u8 as char).collect()
}

pub(super) fn oracle(name: &str, args: &[i64]) -> Option<(Vec<u8>, Vec<i64>)> {
    let mut a = Asm::new();
    let mut callouts: Vec<Callout> = Vec::new();
    let mut stubs: Vec<(Label, u32)> = Vec::new();
    let mut outside: Vec<Label> = Vec::new();
    let mut pre: Vec<u8> = Vec::new();
    let r = |k: usize| args[k] as Reg;
    let flag = |k: usize| args[k] != 0;
    match name {
        "box-reg" => box_reg(&mut a, &mut callouts, r(0), flag(1)),
        "unbox-reg" => unbox_reg(&mut a, &mut callouts, r(0)),
        "unbox-f64" => unbox_f64(&mut a, r(0)),
        "raw-entry" => raw_entry(&mut a, args[0] as u8),
        "raw-entry-skip" => pre.extend((raw_entry_skip(args[0] as u8) as u16).to_le_bytes()),
        "take-raw-f64" => take_raw_f64(&mut a),
        "raw-return" => raw_return(&mut a, &mut callouts),
        "box-f64" => box_f64(&mut a, &mut callouts, r(0)),
        "box-bits" => {
            let slow = a.label();
            outside.push(slow);
            box_bits(&mut a, slow);
        }
        "unbox-to" => {
            let rep = rep_of(args[1]);
            unbox_to(&mut a, &mut callouts, args[0] as usize, rep);
        }
        "convert" => {
            let general = a.label();
            outside.push(general);
            let cs: Vec<Convert> = args[1..].iter().map(|&c| convert_of(c)).collect();
            convert(&mut a, &mut callouts, &cs, general, r(0));
        }
        "f64-of-int" => f64_of_int(&mut a, &mut callouts, args[0] as usize),
        "int-of-f64" => int_of_f64(&mut a, &mut callouts, &mut stubs, args[0] as usize),
        "float-test" => pre.push(float_test(&mut a, flag(0), &name_at(args, 1)) as u8),
        "f64-fast" => f64_fast(&mut a, &name_at(args, 1), r(0)),
        "f32-fast" => pre.push(f32_fast(&mut a, &name_at(args, 1), r(0)) as u8),
        "wrap-small" => wrap_small(&mut a, flag(0), args[1] as u32),
        "raw-fast" => raw_fast(&mut a, &mut stubs, flag(0), &name_at(args, 2), r(1)),
        "narrow-fast" => {
            let slow = a.label();
            outside.push(slow);
            pre.push(narrow_fast(&mut a, &name_at(args, 1), r(0), slow) as u8);
        }
        // Has an overflow, x, y (-1 with an immediate), the immediate, into,
        // the primitive, a difference, has a branch, taken when true: its
        // labels entry, overflow, back and branch, made in that order.
        "int-slow" => {
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
                imm: (args[2] < 0).then_some(args[3] as i32),
                into: r(4),
                prim: args[5] as usize,
                sub: flag(6),
                branch: branch.map(|l| (l, flag(8))),
            };
            s.emit(&mut a, &mut callouts, &mut stubs);
        }
        _ => return None,
    }
    for l in outside {
        a.bind(l);
    }
    // Something after them, for `finish` to look at where a jump goes.
    a.es(&[0x0F, 0x0B]);
    place_stubs(&mut a, &stubs);
    pre.extend(a.finish().expect("placed"));
    Some((pre, callouts.into_iter().map(super::super::fx::callout_code).collect()))
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

/// A conversion, as `native-reps-sig` numbers it.
fn convert_of(c: i64) -> Convert {
    let (r, rep) = (((c / 8) % 16) as usize, rep_of(c % 8));
    match c / 128 {
        0 => Convert::Box { r, rep },
        1 => Convert::Unbox { r, rep },
        _ => Convert::Check { r },
    }
}
