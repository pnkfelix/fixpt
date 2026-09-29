//! Register code (PLAN.md 13h′): words for the MacScheme machine, made and
//! checked here as cellular words are in `cellular.rs`.

use crate::heap::Heap;
use crate::layout::regcode::{OPS, REGS};
use crate::layout::cellular::{PRIMITIVES, ROUTINES, WORD_CELL0, WORD_ENTRY, WORD_NAME, WORD_TWIN};
use crate::layout::kind;
use crate::value::Value;

const KIND: u8 = kind("register-code");

impl Heap {
    /// A register word named `name`, standing for the cellular word `twin`,
    /// whose cells are `cells`: made only if well formed, so that a machine
    /// may run it without checking again. Its entry is 0 until a machine
    /// compiles it.
    pub fn make_register_word(&mut self, name: Value, twin: Value, cells: &[Value]) -> Result<Value, String> {
        check(self, twin, cells)?;
        let w = self.make_bloblet(KIND, WORD_CELL0 - 2 + cells.len(), 0, true);
        self.set_bloblet_slot(w, WORD_ENTRY, Value::fixnum(0));
        self.set_bloblet_slot(w, WORD_NAME, name);
        self.set_bloblet_slot(w, WORD_TWIN, twin);
        for (i, c) in cells.iter().enumerate() {
            self.set_bloblet_slot(w, WORD_CELL0 + i, *c);
        }
        Ok(w)
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
            _ if i == 0 => return Err("register code begins `args n`".into()),
            "reg" => count(o(0), n),
            "setreg" => reg(o(0)),
            "movereg" => count(o(0), n) && reg(o(1)),
            "load" | "store" => reg(o(0)) && count(o(1), i64::MAX),
            "save" | "pop" | "stack" | "setstk" | "lexical" => count(o(0), i64::MAX),
            "op1" | "op2" | "op2imm" => count(o(0), PRIMITIVES as i64 - 1) && (name != "op2" || reg(o(1))),
            "field" => o(0).is_fixnum() && o(0).as_fixnum() >= 2,
            "setfield" => o(0).is_fixnum() && o(0).as_fixnum() >= 2 && reg(o(1)),
            "prim" => count(o(0), i64::MAX) && many(o(1)),
            "lambda" => heap.is_cellular_word(o(0)) && many(o(1)),
            "invoke" | "tailinvoke" | "invokeself" => many(o(0)),
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
                o(0).is_bloblet() && heap.is_cellular_word(o(1))
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
