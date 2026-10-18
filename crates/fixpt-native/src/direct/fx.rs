//! The native convention's procedures compiled by the compiler written in
//! FX-26 (`native-direct-x64.fx` and the files beside it): x86_64's
//! `procedure_x64`, step for step, as `native-x64-regs.fx` is register
//! code's `assemble_register_word`. That compiler is this one's oracle: a
//! compile it makes is the same, byte for byte, field for field and
//! call-out for call-out (`fixpt-fx26/tests/native_x64.rs`).
//!
//! The work is shared as for register code (`syn::assemble_reachable_by_fx26`):
//! Rust finds what to compile and places it, FX-26 makes each procedure's
//! code. Here Rust keeps `compile`'s driver: the procedures a closure
//! reaches, each global's binding (`global_value`), refusals, and making
//! the code bloblets (`install`). Before each procedure is made, it asks
//! what `procedure_x64` would ask as it goes (`prepare_x64`, in the same
//! order, so that every procedure has the same number), and gives FX-26
//! the procedure's cells with the answers, as integers ([`FxRequest`]);
//! FX-26 gives back its bytes, its code bloblet's fields and the call-outs
//! it numbered ([`FxEmitted`]).
//!
//! The values the driver holds are not rooted, and running FX-26 may
//! collect: collection is held off from [`DirectMachine::fx_begin`] to
//! [`DirectMachine::fx_finish`] (or [`fx_abandon`]).

use super::{Callout, Compiled, Compiling, DirectMachine, Field, Proc, GLOBAL_WRITES, OPS, ROUTINES};
use fixpt_heap::{Heap, Value};
use std::collections::HashMap;

/// A compile by FX-26 under way: `compile`'s driver, between the
/// procedures FX-26 makes.
pub struct FxCompile {
    procs: Vec<Proc>,
    by_word: HashMap<u64, usize>,
    queue: Vec<usize>,
    resume: Option<usize>,
    refused: std::collections::HashSet<u64>,
    native_masks: HashMap<u64, Option<u8>>,
    closure: Value,
    first: usize,
    free: Vec<Value>,
    /// The values the requests name by number (`FxRequest::ids`), and each
    /// one's number by its bits; the lists of free values a closure field
    /// names (`frees[0]` none).
    values: Vec<Value>,
    value_ids: HashMap<u64, usize>,
    frees: Vec<Vec<Value>>,
    /// The procedure FX-26 is making.
    current: Option<usize>,
}

/// One procedure for FX-26 to make: its name; `head`, what it is given of
/// the compile ([`FxRequest::head`]); and by the index of each of its cells
/// (`WORD_CELL0` on, as the register word has them, not yet split), the
/// cell's bits, high and low halves; the number of the heap value it is
/// (`-1` for a fixnum or an immediate); and what `prepare_x64` found for
/// the instruction starting there (`kind`, `a`, `b`, `c`), as
/// `native-direct-x64.fx` reads them. `errors`: messages a `kind` of -1
/// names by its `a`.
pub struct FxRequest {
    pub name: String,
    pub head: Vec<i64>,
    pub hi: Vec<i64>,
    pub lo: Vec<i64>,
    pub ids: Vec<i64>,
    pub kind: Vec<i64>,
    pub a: Vec<i64>,
    pub b: Vec<i64>,
    pub c_hi: Vec<i64>,
    pub c_lo: Vec<i64>,
    pub errors: Vec<String>,
}

impl FxRequest {
    /// What `head` holds, by index.
    pub const CALLOUTS: usize = 0;
    pub const INFO_CAPTURES: usize = 1;
    pub const INFO: usize = 2;
    pub const SSE41: usize = 3;
    pub const WORD_ID: usize = 4;
}

/// What FX-26 made of a procedure: its bytes, how many are its own (the
/// rest, its traps'), its code bloblet's fields (`field_code`), the
/// call-outs it numbered from the machine's count (`callout_code`), and
/// why it could not ("" if it could; the call-outs numbered before it
/// stopped are numbered still, as the Rust compiler's are).
pub struct FxEmitted {
    pub code: Vec<u8>,
    pub len: usize,
    pub fields: Vec<i64>,
    pub callouts: Vec<i64>,
    pub err: String,
}

/// A field as FX-26 names it: `Myself` 0, `Code(q)` 1 + 8q, `Const` of
/// value `v` 2 + 8v, `Cell` of value `v` 3 + 8v, `Closure(q, frees[f])`
/// 4 + 8(q + 2^20 f).
fn field_of(c: &FxCompile, code: i64) -> Result<Field, String> {
    let (tag, n) = (code & 7, (code >> 3) as usize);
    let value = |v: usize| c.values.get(v).copied().ok_or_else(|| format!("no value {v}"));
    Ok(match tag {
        0 => Field::Myself,
        1 => Field::Code(n),
        2 => Field::Const(value(n)?),
        3 => Field::Cell(value(n)?),
        4 => Field::Closure(n % (1 << 20), c.frees.get(n >> 20).cloned().ok_or("no free values")?),
        _ => return Err(format!("no field {code}")),
    })
}

/// A call-out as FX-26 numbers its kind, and its operands: the kind, plus
/// 32 times the first operand, plus 32 · 4096 times the second.
pub fn callout_of(code: i64) -> Result<Callout, String> {
    let (kind, a, b) = (code % 32, ((code / 32) % 4096) as usize, (code / (32 * 4096)) as usize);
    Ok(match kind {
        0 => Callout::Cons,
        1 => Callout::Bloblet,
        2 => Callout::Prim { p: a, n: b },
        3 => Callout::Closure { n: a },
        4 => Callout::ClosureAny,
        5 => Callout::RegionClosure { n: a },
        6 => Callout::FieldRef,
        7 => Callout::Foreign,
        8 => Callout::Abort,
        9 => Callout::Capture { whole: a != 0, once: b != 0 },
        10 => Callout::Reinstate,
        11 => Callout::FirstMark,
        12 => Callout::CurrentMarks,
        13 => Callout::MarksOf,
        14 => Callout::Rest,
        15 => Callout::Pure { p: a, n: b },
        16 => Callout::Box { signed: a != 0 },
        17 => Callout::Unbox,
        18 => Callout::BoxF64,
        19 => Callout::Underflow,
        20 => Callout::Overflow,
        21 => Callout::Poll,
        22 => Callout::PollDone,
        23 => Callout::Failed,
        _ => return Err(format!("no call-out {code}")),
    })
}

/// The other way, for the layout FX-26 is given and the oracle's checks.
pub fn callout_code(c: Callout) -> i64 {
    let k = |kind: i64, a: usize, b: usize| kind + 32 * (a as i64 + 4096 * b as i64);
    match c {
        Callout::Cons => k(0, 0, 0),
        Callout::Bloblet => k(1, 0, 0),
        Callout::Prim { p, n } => k(2, p, n),
        Callout::Closure { n } => k(3, n, 0),
        Callout::ClosureAny => k(4, 0, 0),
        Callout::RegionClosure { n } => k(5, n, 0),
        Callout::FieldRef => k(6, 0, 0),
        Callout::Foreign => k(7, 0, 0),
        Callout::Abort => k(8, 0, 0),
        Callout::Capture { whole, once } => k(9, whole as usize, once as usize),
        Callout::Reinstate => k(10, 0, 0),
        Callout::FirstMark => k(11, 0, 0),
        Callout::CurrentMarks => k(12, 0, 0),
        Callout::MarksOf => k(13, 0, 0),
        Callout::Rest => k(14, 0, 0),
        Callout::Pure { p, n } => k(15, p, n),
        Callout::Box { signed } => k(16, signed as usize, 0),
        Callout::Unbox => k(17, 0, 0),
        Callout::BoxF64 => k(18, 0, 0),
        Callout::Underflow => k(19, 0, 0),
        Callout::Overflow => k(20, 0, 0),
        Callout::Poll => k(21, 0, 0),
        Callout::PollDone => k(22, 0, 0),
        Callout::Failed => k(23, 0, 0),
    }
}

/// `f` on a `Compiling` of `c`'s driver, put back after.
fn driving<T>(heap: &Heap, callouts: &mut Vec<Callout>, c: &mut FxCompile, f: impl FnOnce(&mut Compiling<'_>) -> T) -> T {
    let mut k = Compiling {
        heap,
        procs: std::mem::take(&mut c.procs),
        by_word: std::mem::take(&mut c.by_word),
        queue: std::mem::take(&mut c.queue),
        callouts,
        resume: c.resume,
        refused: std::mem::take(&mut c.refused),
        native_masks: std::mem::take(&mut c.native_masks),
    };
    let r = f(&mut k);
    (c.procs, c.by_word, c.queue, c.resume, c.refused, c.native_masks) = (k.procs, k.by_word, k.queue, k.resume, k.refused, k.native_masks);
    r
}

impl FxCompile {
    /// The driver as `compile` starts it, refusing `refused`.
    fn start(&mut self, heap: &Heap, callouts: &mut Vec<Callout>) -> Result<(), String> {
        let closure = self.closure;
        let first = driving(heap, callouts, self, |k| -> Result<(usize, Vec<Value>), String> {
            let (word, free) = k.closure_parts(closure).ok_or("not a closure of cellular code")?;
            Ok((k.proc_of(word)?, free))
        })?;
        (self.first, self.free) = first;
        Ok(())
    }
}

impl DirectMachine {
    /// Compile `closure` as `compile` does, but each procedure's code made
    /// by FX-26: the driver, started. Collection is held off until
    /// [`fx_finish`](DirectMachine::fx_finish) or [`fx_abandon`].
    pub fn fx_begin(&mut self, heap: &mut Heap, closure: Value) -> Result<FxCompile, String> {
        heap.inhibit_collection();
        let mut c = FxCompile {
            procs: Vec::new(),
            by_word: HashMap::new(),
            queue: Vec::new(),
            resume: None,
            refused: std::collections::HashSet::new(),
            native_masks: HashMap::new(),
            closure,
            first: 0,
            free: Vec::new(),
            values: Vec::new(),
            value_ids: HashMap::new(),
            frees: vec![Vec::new()],
            current: None,
        };
        if let Err(e) = c.start(heap, &mut self.callouts) {
            heap.allow_collection();
            return Err(e);
        }
        Ok(c)
    }

    /// The next procedure for FX-26 to make, or none: the compile is made.
    /// An error ends the compile ([`fx_abandon`] it).
    pub fn fx_next(&mut self, heap: &Heap, c: &mut FxCompile) -> Result<Option<FxRequest>, String> {
        loop {
            let Some(p) = c.queue.pop() else { return Ok(None) };
            c.current = Some(p);
            let prepared = {
                let mut ids = std::mem::take(&mut c.values);
                let mut value_ids = std::mem::take(&mut c.value_ids);
                let mut frees = std::mem::take(&mut c.frees);
                let r = driving(heap, &mut self.callouts, c, |k| k.prepare_x64(p, &mut |v| intern(&mut ids, &mut value_ids, v), &mut |f| free_of(&mut frees, f)));
                (c.values, c.value_ids, c.frees) = (ids, value_ids, frees);
                r
            };
            match prepared {
                Ok(mut r) => {
                    r.head[FxRequest::CALLOUTS] = self.callouts.len() as i64;
                    let word = c.procs[p].word;
                    r.head[FxRequest::WORD_ID] = intern(&mut c.values, &mut c.value_ids, word);
                    return Ok(Some(r));
                }
                // As `procedure_x64` failing before it made any code.
                Err(e) => self.fx_refuse(heap, c, p, e)?,
            }
        }
    }

    /// FX-26's code for the procedure [`fx_next`](DirectMachine::fx_next)
    /// asked for. An error ends the compile ([`fx_abandon`] it).
    pub fn fx_emitted(&mut self, heap: &Heap, c: &mut FxCompile, out: FxEmitted) -> Result<(), String> {
        let p = c.current.take().ok_or("no procedure asked for")?;
        for &k in &out.callouts {
            self.callouts.push(callout_of(k)?);
        }
        if !out.err.is_empty() {
            return self.fx_refuse(heap, c, p, out.err);
        }
        let fields = out.fields.iter().map(|&f| field_of(c, f)).collect::<Result<Vec<Field>, String>>()?;
        let proc_ = &mut c.procs[p];
        proc_.fields = fields;
        proc_.code = out.code;
        proc_.len = out.len;
        Ok(())
    }

    /// Procedure `p` could not be compiled, for `why`: as in `compile`, the
    /// whole compile fails for the first or for one that is no global's;
    /// else it is refused, and the rest compiled again without it.
    fn fx_refuse(&mut self, heap: &Heap, c: &mut FxCompile, p: usize, why: String) -> Result<(), String> {
        if p == c.first || !c.procs[p].global {
            return Err(why);
        }
        let mut refused = std::mem::take(&mut c.refused);
        refused.insert(c.procs[p].word.raw());
        (c.procs, c.by_word, c.queue, c.resume, c.native_masks) = (Vec::new(), HashMap::new(), Vec::new(), None, HashMap::new());
        c.refused = refused;
        c.start(heap, &mut self.callouts)
    }

    /// The compile made, its code bloblets placed, and collection allowed
    /// again: what `compile` gives.
    pub fn fx_finish(&mut self, heap: &mut Heap, c: FxCompile) -> Result<Vec<(String, Compiled)>, String> {
        let r = super::install(heap, &c.procs, c.first, &c.free);
        heap.allow_collection();
        r
    }
}

/// A compile given up: collection allowed again.
pub fn fx_abandon(heap: &mut Heap, _c: FxCompile) {
    heap.allow_collection();
}

fn intern(values: &mut Vec<Value>, ids: &mut HashMap<u64, usize>, v: Value) -> i64 {
    let n = values.len();
    let id = *ids.entry(v.raw()).or_insert(n);
    if id == n {
        values.push(v);
    }
    id as i64
}

fn free_of(frees: &mut Vec<Vec<Value>>, free: Vec<Value>) -> i64 {
    match frees.iter().position(|f| *f == free) {
        Some(k) => k as i64,
        None => {
            frees.push(free);
            frees.len() as i64 - 1
        }
    }
}

impl Compiling<'_> {
    /// What `procedure_x64` asks the driver as it compiles procedure `p`,
    /// asked in the same order, for FX-26 ([`FxRequest`]): first, of the
    /// calls, which callees take arguments raw (each global called, bound
    /// or not, and each closure constant called); then, instruction by
    /// instruction, the procedure each `const` of a word or closure, each
    /// `global` and each `lambda` names, and the continuation procedure
    /// for a capture. What fails before any code (a global's binding) is
    /// this one's error, as `procedure_x64`'s; what fails later is noted at
    /// its instruction, for FX-26 to stop there. Values are numbered by
    /// `id`, lists of free values by `free_id`.
    pub(super) fn prepare_x64(&mut self, p: usize, id: &mut dyn FnMut(Value) -> i64, free_id: &mut dyn FnMut(Vec<Value>) -> i64) -> Result<FxRequest, String> {
        let h = self.heap;
        let (word, rw) = (self.procs[p].word, self.procs[p].rw);
        let raw_cells: Vec<Value> = (fixpt_heap::layout::cellular::WORD_CELL0..=h.bloblet_head(rw).fields).map(|k| h.bloblet_slot(rw, k)).collect();
        let cells = super::register_cells(h, rw);
        let name = self.name(word);
        let n = cells.len();
        let mut r = FxRequest {
            name: name.clone(),
            head: vec![0; 5],
            hi: Vec::with_capacity(n),
            lo: Vec::with_capacity(n),
            ids: Vec::with_capacity(n),
            kind: vec![0; n],
            a: vec![0; n],
            b: vec![0; n],
            c_hi: vec![0; n],
            c_lo: vec![0; n],
            errors: Vec::new(),
        };
        let immediate = |v: Value| v.is_fixnum() || v.raw() & 7 == 3;
        for &v in &raw_cells {
            r.hi.push((v.raw() >> 32) as i64);
            r.lo.push((v.raw() & 0xffff_ffff) as i64);
            r.ids.push(if immediate(v) { -1 } else { id(v) });
        }
        let mut starts = Vec::new();
        let mut i = 0;
        while i < n {
            starts.push(i);
            i += 1 + OPS[cells[i].as_fixnum() as usize].1;
        }
        let op_at = |j: usize| OPS[cells[j].as_fixnum() as usize].0;
        let called = |j: usize| {
            let at = starts.iter().position(|&s| s == j).expect("an instruction");
            starts[at + 1..].iter().copied().find(|&c| op_at(c) != "pop").filter(|&c| matches!(op_at(c), "invoke" | "tailinvoke"))
        };
        // The callees, as `procedure_x64` finds them, before any code.
        self.params_of(p);
        for &j in &starts {
            let Some(c) = called(j) else { continue };
            let q = match op_at(j) {
                "global" => match self.global_value(cells[j + 1]).map_err(|e| format!("`{name}` calls {e}"))? {
                    Field::Code(q) => Some(q),
                    Field::Const(v) => {
                        r.a[c] = self.native_params(v).unwrap_or(0) as i64;
                        None
                    }
                    _ => None,
                },
                "const" => match self.closure_parts(cells[j + 1]) {
                    Some((word, free)) if !h.is_cellular_word(cells[j + 1]) && free.is_empty() && self.name(word) != "undefined" => {
                        Some(self.proc_of(word).map_err(|e| format!("`{name}` calls {e}"))?)
                    }
                    _ => None,
                },
                _ => None,
            };
            if let Some(q) = q {
                r.a[c] = self.params_of(q) as i64;
            }
        }
        let fail = |r: &mut FxRequest, i: usize, e: String| {
            r.kind[i] = -1;
            r.a[i] = r.errors.len() as i64;
            r.errors.push(e);
        };
        for &i in &starts {
            let o = |j: usize| cells[i + 1 + j];
            match op_at(i) {
                "const" => {
                    let v = o(0);
                    if immediate(v) {
                    } else if h.is_cellular_word(v) {
                        match self.proc_of(v) {
                            Ok(q) => (r.kind[i], r.a[i]) = (1, q as i64),
                            Err(e) => fail(&mut r, i, format!("`{name}` makes a closure of {e}")),
                        }
                    } else if let Some((word, free)) = self.closure_parts(v)
                        && free.is_empty()
                        && self.name(word) != "undefined"
                    {
                        match self.proc_of(word) {
                            Ok(q) => (r.kind[i], r.a[i]) = (2, q as i64),
                            Err(e) => fail(&mut r, i, format!("`{name}` calls {e}")),
                        }
                    }
                }
                "global" => {
                    let cell = o(0);
                    let writes = h.bloblet_slot(cell, GLOBAL_WRITES).raw();
                    (r.c_hi[i], r.c_lo[i]) = ((writes >> 32) as i64, (writes & 0xffff_ffff) as i64);
                    match self.global_value(cell) {
                        Ok(Field::Cell(_)) => r.kind[i] = 0,
                        Ok(Field::Code(q)) => (r.kind[i], r.a[i]) = (1, q as i64),
                        Ok(Field::Closure(q, free)) => (r.kind[i], r.a[i], r.b[i]) = (2, q as i64, free_id(free)),
                        Ok(Field::Const(v)) => (r.kind[i], r.a[i]) = (3, id(v)),
                        Ok(Field::Myself) => unreachable!("a global's value"),
                        Err(e) => fail(&mut r, i, format!("`{name}` calls {e}")),
                    }
                }
                "lambda" => match self.proc_of(o(0)) {
                    Ok(q) => (r.kind[i], r.a[i]) = (1, q as i64),
                    Err(e) => fail(&mut r, i, format!("`{name}` makes a closure of {e}")),
                },
                "cellular"
                    if matches!(
                        ROUTINES.get(o(0).as_fixnum() as usize).map(|r| r.0),
                        Some("callcc" | "callcomp" | "ncallcc" | "ncallcomp" | "callone" | "ncallone")
                    ) =>
                {
                    r.b[i] = self.resume_proc() as i64;
                }
                _ => {}
            }
        }
        let arity = self.procs[p].arity;
        r.head[FxRequest::INFO_CAPTURES] = super::overflow_info(arity, true) as i64;
        r.head[FxRequest::INFO] = super::overflow_info(arity, false) as i64;
        r.head[FxRequest::SSE41] = super::x64::sse41() as i64;
        Ok(r)
    }
}
