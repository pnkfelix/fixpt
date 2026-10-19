//! This pass's results on a register word, for the pass written in FX-26
//! (`native-reps.fx`) to be checked against (`fixpt-fx26/tests/native_reps.rs`),
//! in the numbers that one uses: a representation (`Rep`) `undefined` 0,
//! `value` 1, `raw signed` 2, `raw unsigned` 3, `f64` 4, `fix` 5; nine of
//! them one int, three bits each, `RESULT`'s lowest; a conversion
//! (`Convert`) 128 times its kind (box 0, unbox 1, check 2) plus 8 times its
//! register plus its representation; masks of registers, bit `r` for
//! register `r`.

use super::super::OPS;
use super::{Calls, Convert, Rep, RawOp};
use fixpt_heap::{Heap, Value};

/// A representation's number.
fn rep_code(r: Rep) -> i64 {
    match r {
        Rep::Undefined => 0,
        Rep::Value => 1,
        Rep::Raw { signed: true } => 2,
        Rep::Raw { signed: false } => 3,
        Rep::F64 => 4,
        Rep::Fix => 5,
    }
}

fn rep_of(code: i64) -> Rep {
    match code {
        1 => Rep::Value,
        2 => Rep::Raw { signed: true },
        3 => Rep::Raw { signed: false },
        4 => Rep::F64,
        5 => Rep::Fix,
        _ => Rep::Undefined,
    }
}

/// Nine representations, packed.
fn pack(reps: &super::Reps) -> i64 {
    reps.iter().enumerate().map(|(r, &rep)| rep_code(rep) << (3 * r)).sum()
}

fn unpack(p: i64) -> super::Reps {
    std::array::from_fn(|r| rep_of((p >> (3 * r)) & 7))
}

/// A conversion's number.
fn convert_code(c: Convert) -> i64 {
    match c {
        Convert::Box { r, rep } => 8 * r as i64 + rep_code(rep),
        Convert::Unbox { r, rep } => 128 + 8 * r as i64 + rep_code(rep),
        Convert::Check { r } => 256 + 8 * r as i64,
    }
}

/// One version's results: the representations where each instruction
/// starts and ends (`reps_of`), and the conversions `step` gives before
/// each, from where it starts, as `procedure_x64` calls it.
pub struct Version {
    pub fast: bool,
    pub callees: Vec<u8>,
    pub ins: Vec<i64>,
    pub outs: Vec<i64>,
    pub steps: Vec<Vec<i64>>,
}

/// What the pass computes on a register word, as `direct.rs` uses it.
pub struct Facts {
    /// The cells as `register_cells` gives them, split (`split_slots`):
    /// each one's value as a fixnum (0 for one that is not).
    pub cells: Vec<i64>,
    pub starts: Vec<usize>,
    /// The frame's slots, from `save` (-1 for no frame).
    pub slots: i64,
    pub raw: Vec<bool>,
    pub params: i64,
    pub raw_refs: Vec<bool>,
    pub live: Vec<i64>,
    pub versions: Vec<Version>,
}

/// The pass on register word `rw`. Each version is computed for the fixnum
/// version and the general one, each with no callee known and with every
/// call's callee taking REG1 and REG3 raw (0b101).
pub fn facts(h: &Heap, rw: Value) -> Facts {
    let cells = super::super::register_cells(h, rw);
    let prim = |p: usize| fixpt_runtime::PRIMITIVES.get(p).map_or("?", |d| d.name);
    let (mut starts, mut frame, mut i) = (Vec::new(), None, 0);
    while i < cells.len() {
        starts.push(i);
        let (op, n, _) = OPS[cells[i].as_fixnum() as usize];
        if op == "save" {
            frame = Some(cells[i + 1].as_fixnum() as usize);
        }
        i += 1 + n;
    }
    let raw = frame.map_or(Vec::new(), |m| super::raw_slots(&cells, &starts, &prim, m));
    let params = super::raw_params(&cells, &starts, &prim, &raw);
    let raw_refs = super::raw_refs(&cells, &starts, &prim, &raw);
    let live = super::live_in(&cells, &starts, &prim, &raw).iter().map(|l| (0..9).filter(|&r| l[r]).map(|r| 1 << r).sum()).collect();
    let op_at = |j: usize| OPS[cells[j].as_fixnum() as usize].0;
    let mut versions = Vec::new();
    for fast in [true, false] {
        for known in [false, true] {
            let callees: Vec<u8> = starts.iter().map(|&j| if known && matches!(op_at(j), "invoke" | "tailinvoke") { 0b101 } else { 0 }).collect();
            let (ins, outs) = super::reps_of(&cells, &starts, &prim, fast, &raw, params, &callees);
            let steps = starts
                .iter()
                .enumerate()
                .map(|(si, &i)| {
                    let o = |j: usize| cells[i + 1 + j];
                    let mut reps = ins[si];
                    let calls = Calls { own: params, callee: callees[si] };
                    super::step(op_at(i), &o, &prim, raw_refs[si], fast, &raw, calls, &mut reps).into_iter().map(convert_code).collect()
                })
                .collect();
            versions.push(Version { fast, callees, ins: ins.iter().map(pack).collect(), outs: outs.iter().map(pack).collect(), steps });
        }
    }
    Facts {
        cells: cells.iter().map(|c| if c.is_fixnum() { c.as_fixnum() } else { 0 }).collect(),
        starts,
        slots: frame.map_or(-1, |m| m as i64),
        raw,
        params: params as i64,
        raw_refs,
        live,
        versions,
    }
}

/// `unboxes` of packed representations, each 8 times its register plus
/// its representation.
pub fn unboxes(from: i64, to: i64) -> Vec<i64> {
    super::unboxes(&unpack(from), &unpack(to)).into_iter().map(|(r, rep)| 8 * r as i64 + rep_code(rep)).collect()
}

/// `checks` of packed representations, `live` a mask.
pub fn checks(from: i64, to: i64, live: i64) -> Vec<i64> {
    let live: [bool; 9] = std::array::from_fn(|r| live & 1 << r != 0);
    super::checks(&unpack(from), &unpack(to), &live).into_iter().map(|r| r as i64).collect()
}

/// `join` of packed representations.
pub fn join(a: i64, b: i64) -> i64 {
    pack(&super::join(&unpack(a), &unpack(b)))
}

/// `raw_op` of a primitive's name: its kind (0 none, 1 an integer's, 2 an
/// `f64`'s), whether signed, and what.
pub fn raw_op(name: &str) -> (i64, bool, String) {
    match super::raw_op(name) {
        None => (0, false, String::new()),
        Some(RawOp::Int { signed, what }) => (1, signed, what.to_string()),
        Some(RawOp::F64 { what }) => (2, false, what.to_string()),
    }
}
