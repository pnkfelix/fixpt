//! Register code (PLAN.md 13h′): words for the MacScheme machine, made and
//! checked here as cellular words are in `cellular.rs`.

use crate::heap::Heap;
use crate::layout::regcode::{OPS, REGS};
use crate::layout::cellular::{PRIMITIVES, ROUTINES, WORD_CELL0, WORD_ENTRY, WORD_NAME, WORD_TWIN};
use crate::layout::kind;
use crate::value::Value;

const KIND: u8 = kind("register-code");

thread_local! {
    /// The source register words made now are compiled from (`set_source`).
    static SOURCE: std::cell::Cell<u32> = const { std::cell::Cell::new(0) };
}

/// Register words made from now on on this thread are compiled from the
/// source numbered `id`: a text a session keeps, by which a debugger finds
/// what file and line a place is (`fixpt_native::jitdebug`). 0 for none.
pub fn set_source(id: u32) {
    SOURCE.with(|s| s.set(id));
}

/// The source register words are made from now.
pub fn source() -> u32 {
    SOURCE.with(|s| s.get())
}

/// A register word's suffix: its source, then each place, its cell's index
/// after the one before and the place, LEB128s; nothing if it has none.
fn encode_places(source: u32, places: &[(usize, i64)]) -> Vec<u8> {
    if places.is_empty() {
        return Vec::new();
    }
    let mut out = Vec::new();
    let uleb = |out: &mut Vec<u8>, mut v: u64| loop {
        let b = (v & 0x7f) as u8;
        v >>= 7;
        if v == 0 {
            out.push(b);
            break;
        }
        out.push(b | 0x80);
    };
    uleb(&mut out, source as u64);
    let mut last = 0;
    for &(k, p) in places {
        uleb(&mut out, (k - last) as u64);
        last = k;
        uleb(&mut out, (p + 1) as u64);
    }
    out
}

fn decode_places(bytes: &[u8]) -> Option<(u32, Vec<(usize, i64)>)> {
    let mut i = 0;
    let mut uleb = || -> Option<u64> {
        let (mut v, mut shift) = (0u64, 0);
        loop {
            let b = *bytes.get(i)?;
            i += 1;
            v |= ((b & 0x7f) as u64) << shift;
            if b & 0x80 == 0 {
                return Some(v);
            }
            shift += 7;
        }
    };
    let source = uleb()? as u32;
    let (mut out, mut at) = (Vec::new(), 0);
    while let Some(d) = uleb() {
        at += d as usize;
        out.push((at, uleb()? as i64 - 1));
    }
    Some((source, out))
}

impl Heap {
    /// A register word named `name`, standing for the cellular word `twin`,
    /// whose cells are `cells`: made only if well formed, so that a machine
    /// may run it without checking again. Its entry is 0 until a machine
    /// compiles it.
    pub fn make_register_word(&mut self, name: Value, twin: Value, cells: &[Value], places: &[(usize, i64)]) -> Result<Value, String> {
        check(self, twin, cells)?;
        let bytes = encode_places(source(), places);
        let w = self.make_bloblet(KIND, WORD_CELL0 - 2 + cells.len(), bytes.len(), true);
        self.set_bloblet_slot(w, WORD_ENTRY, Value::fixnum(0));
        self.set_bloblet_slot(w, WORD_NAME, name);
        self.set_bloblet_slot(w, WORD_TWIN, twin);
        for (i, c) in cells.iter().enumerate() {
            self.set_bloblet_slot(w, WORD_CELL0 + i, *c);
        }
        self.set_bloblet_bytes(w, 0, &bytes).map_err(|e| format!("{e:?}"))?;
        Ok(w)
    }

    /// Where register word `w`'s expressions start: the source its places
    /// are in ([`set_source`]), and at each cell (counted from
    /// `WORD_CELL0`) where the place changes, the cell and the place (as
    /// the compilers' `place_of`, -1 for none). None if it has none.
    pub fn register_places(&self, w: Value) -> Option<(u32, Vec<(usize, i64)>)> {
        decode_places(&self.bloblet_bytes(w))
    }

    pub fn is_register_word(&self, v: Value) -> bool {
        v.is_bloblet() && self.bloblet_kind(v) == KIND
    }
}

fn check(heap: &Heap, twin: Value, cells: &[Value]) -> Result<(), String> {
    if !heap.is_cellular_word(twin) {
        return Err("a register word stands for a cellular word".into());
    }
    let count = |v: Value, max: i64| v.is_fixnum() && (0..=max).contains(&v.as_fixnum());
    let mut starts = vec![false; cells.len() + 1];
    let mut branches = Vec::new();
    let (mut i, mut last) = (0, "");
    while i < cells.len() {
        starts[i] = true;
        let c = cells[i];
        if !count(c, OPS.len() as i64 - 1) {
            return Err(format!("cell {i}: no register operation"));
        }
        let (name, ops, _) = OPS[c.as_fixnum() as usize];
        if i + ops >= cells.len() + usize::from(ops == 0) {
            return Err(format!("cell {i}: `{name}` needs {ops} operand(s)"));
        }
        let o = |j: usize| cells[i + 1 + j];
        let reg = |v: Value| count(v, REGS as i64) && v.as_fixnum() >= 1;
        let n = REGS as i64;
        // How many values an operation takes: past `REGS`, the rest are a
        // list in the last register (Larceny's convention).
        let many = |v: Value| count(v, 1 << 16);
        let ok = match name {
            "args" => i == 0 && many(o(0)),
            "vargs" => i == 0,
            _ if i == 0 => return Err("register code begins `args n` or `vargs`".into()),
            "reg" => count(o(0), n),
            "setreg" => reg(o(0)),
            "movereg" => count(o(0), n) && reg(o(1)),
            "load" | "store" => reg(o(0)) && count(o(1), i64::MAX),
            "save" | "pop" | "stack" | "setstk" | "lexical" => count(o(0), i64::MAX),
            "op1" | "op2" | "op2imm" => count(o(0), PRIMITIVES as i64 - 1) && (name != "op2" || reg(o(1))),
            "field" => o(0).is_fixnum() && o(0).as_fixnum() >= 2,
            "setfield" => o(0).is_fixnum() && o(0).as_fixnum() >= 2 && reg(o(1)),
            "prim" => count(o(0), i64::MAX) && many(o(1)),
            "prim1" | "prim2imm" => count(o(0), i64::MAX),
            "prim2" => count(o(0), i64::MAX) && reg(o(1)),
            "prim3imm" => count(o(0), i64::MAX) && reg(o(2)),
            "lambda" => {
                use crate::layout::cellular::routine;
                let r = o(2);
                heap.is_cellular_word(o(0)) && many(o(1)) && r.is_fixnum() && [routine("closure"), routine("nclosure")].contains(&(r.as_fixnum() as u64))
            }
            "invoke" | "tailinvoke" => many(o(0)) && count(o(1), crate::layout::regcode::CONVS.len() as i64 - 1),
            "invokeself" => many(o(0)),
            "cellular" => count(o(0), ROUTINES.len() as i64 - 1) && many(o(1)),
            "global" | "setglbl" => o(0).is_bloblet(),
            "branch" | "branchf" | "brancht" => {
                if !o(0).is_fixnum() {
                    return Err(format!("cell {i}: a branch's offset is a fixnum"));
                }
                branches.push((i, i as i64 + 2 + o(0).as_fixnum()));
                true
            }
            "global-guard" => {
                if !o(2).is_fixnum() {
                    return Err(format!("cell {i}: a guard's offset is a fixnum"));
                }
                branches.push((i, i as i64 + 4 + o(2).as_fixnum()));
                o(0).is_bloblet()
                    && heap.bloblet_head(o(0)).fields >= crate::layout::cellular::GLOBAL_FIELDS
                    && o(1).is_fixnum()
                    && o(1).as_fixnum() >= 0
            }
            _ => true,
        };
        if !ok {
            return Err(format!("cell {i}: `{name}` has an operand out of range"));
        }
        last = name;
        i += 1 + ops;
    }
    for (at, to) in branches {
        if to < 0 || to as usize > cells.len() || !starts[to as usize] {
            return Err(format!("cell {at}: the branch lands on no instruction"));
        }
    }
    if !matches!(last, "return" | "tailinvoke" | "branch") {
        return Err("register code must not run past its last cell".into());
    }
    Ok(())
}
