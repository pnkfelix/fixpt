//! The Rust compiler's pieces of the primitives' instructions by name, for
//! `fx_arm64::oracle` (`native-direct-arm64-strings.fx`): `pure_fast` and
//! `string_eq`, each run in an `Asm` of its own (`oracle_asm::harness`).
//! Each piece's arguments are integers: registers, and a name as its
//! bytes, last. `pure-fast` answers whether it has a fast path, a byte (1
//! or 0) before its code; its `slow` is bound after it.

use super::super::*;
use super::oracle_asm::harness;

/// The name at the end of `args`, from `k` on.
fn name_at(args: &[i64], k: usize) -> String {
    args[k..].iter().map(|&b| b as u8 as char).collect()
}

pub(super) fn oracle(name: &str, args: &[i64]) -> Option<(Vec<u8>, Vec<i64>)> {
    let r = |k: usize| args[k] as Reg;
    Some(match name {
        "pure-fast" => harness(|a, _, _, outside, pre| {
            let slow = a.label();
            outside.push(slow);
            let what = name_at(args, 1);
            pre.push(pure_fast(a, &what, r(0), slow) as u8);
        }),
        "string-eq" => harness(|a, _, _, _, _| string_eq(a, r(0), r(1))),
        _ => return None,
    })
}
