//! The heap's fast paths of `direct.rs` by name (`fx_arm64::oracle`), for
//! `native-direct-arm64-flat.fx` to be checked against: each in an `Asm`
//! of its own (`super::oracle_asm::harness`), the labels it is given
//! (`slow`, then `done`) made before it and bound after it, in that order.
//! `shape-fast`'s name is its arguments' bytes, and what it answers (1 if
//! it knew the shape, else 0) its `pre`.

use super::super::*;
use super::oracle_asm::harness;

pub(super) fn oracle(name: &str, args: &[i64]) -> Option<(Vec<u8>, Vec<i64>)> {
    let r = |k: usize| args[k] as Reg;
    let b = |k: usize| args[k] != 0;
    // A piece given `slow` and `done`, whether it uses them or not.
    let run = |piece: &dyn Fn(&mut Asm, Label, Label)| {
        harness(|a, _, _, outside, _| {
            let (slow, done) = (a.label(), a.label());
            outside.extend([slow, done]);
            piece(a, slow, done);
        })
    };
    Some(match name {
        "flat-count" => run(&|a, _, _| flat_count(a, r(0), r(1))),
        "flat-element" => run(&|a, slow, _| flat_element(a, r(0), r(1), slow)),
        "flat-ref" => run(&|a, slow, _| flat_ref(a, r(0), slow)),
        "box-bits" => run(&|a, slow, _| box_bits(a, slow)),
        "suffix-owner" => run(&|a, slow, _| suffix_owner(a, r(0), slow)),
        "suffix-writable" => run(&|a, slow, _| suffix_writable(a, r(0), slow)),
        "suffix-store" => run(&|a, slow, _| suffix_store(a, args[0], r(1), b(2), slow)),
        "blobref-index" => run(&|a, slow, _| blobref_index(a, args[0], r(1), slow)),
        "flat-variant" => run(&|a, slow, _| flat_variant(a, args[0], r(1), slow)),
        "blobref-at" => run(&|a, slow, _| blobref_at(a, args[0], slow)),
        "suffix-step" => run(&|a, slow, _| suffix_step(a, args[0], slow)),
        "suffix-fits" => run(&|a, slow, _| suffix_fits(a, args[0], slow)),
        "suffix-length" => run(&|a, slow, _| suffix_length(a, args[0], slow)),
        "suffix-index" => run(&|a, slow, _| suffix_index(a, slow)),
        "flat-tag" => run(&|a, slow, _| flat_tag(a, args[0], slow)),
        "suffix-get" => run(&|a, slow, _| suffix_get(a, args[0], b(1), slow)),
        "suffix-set" => run(&|a, slow, done| suffix_set(a, slow, done)),
        "bytes-set" => run(&|a, slow, done| bytes_set(a, slow, done)),
        "flat-set" => run(&|a, slow, done| flat_set(a, slow, done, b(0))),
        "shape-fast" => harness(|a, _, _, outside, pre| {
            let slow = a.label();
            outside.push(slow);
            let name: String = args.iter().map(|&c| c as u8 as char).collect();
            pre.push(shape_fast(a, &name, slow) as u8);
        }),
        _ => return None,
    })
}
