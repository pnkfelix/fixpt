//! Code in the native convention (`docs/research/native-conventions.md`,
//! step 2): first-order procedures compiled from their register code to
//! machine code that calls by `bl` and returns by `ret`, with frames on a
//! stack of its own, and no ip, data stack, return entry or resume table.
//!
//! The convention, as the note has it, with register code's numbering:
//!
//! | what                 | where                                                      |
//! | -------------------- | ---------------------------------------------------------- |
//! | arguments            | `x1`–`x8` (register code's `REG1`…`REG8`)                  |
//! | result               | `x0` (`RESULT`)                                            |
//! | return address       | `x30`, saved in the frame by a procedure that has one      |
//! | frame link           | `x29`                                                      |
//! | the machine's state  | `x24`, pinned                                              |
//! | fuel                 | `x28`, pinned                                              |
//! | the stack's limit    | `x27`, pinned                                              |
//! | the closure called   | `x10`, as the call enters it; kept in the frame if read    |
//! | code's run address   | `x26`, pinned: a code bloblet's reference plus it          |
//! | values across a call | the frame's slots, `[x29, #16 + 8n]` for slot `n`          |
//!
//! Every register but the pinned ones is the caller's to lose across a
//! call; register code already keeps whatever lives across one in its
//! frame. A procedure with no frame, no call and no loop (a leaf) checks
//! nothing: `(lambda ((x int)) x)` is `mov x0, x1; ret`. One with a frame
//! checks the stack's limit once, on entry, and fuel on entry; a loop
//! checks fuel on its back edge.
//!
//! What is compiled, for now: procedures that capture nothing, whose
//! register code keeps to arguments, immediate constants, registers and
//! frame slots, the integer operations register code does inline, pairs'
//! and bloblets' fields, branches, and calls of themselves or of other such
//! procedures named by globals. Anything else (a call-out, which may
//! collect; a closure made or read; a global read for its value) declines
//! the procedure, and whoever calls it. The collector never runs while
//! this code does, so no frame needs a stack map yet (step 3).
//!
//! A global called is bound when compiling: the code calls the procedure
//! the global held then. That is right for a program whose globals are
//! defined once, which is all this is used for until step 3 gives code
//! bloblets fields to keep their globals in.

use crate::arm64::*;
use crate::codespace::{CodeSpace, Offset};
use fixpt_heap::layout::cellular::{CLOSURE_FREE0, CLOSURE_WORD, ROUTINES, WORD_CELL0, WORD_TWIN};
use fixpt_heap::layout::regcode::OPS;
use fixpt_heap::{Heap, Value};
use std::collections::HashMap;
use std::mem::offset_of;

const RESULT: Reg = 0;
const ST: Reg = 24;
const FUEL: Reg = 28;
/// The native stack's limit, pinned.
const LIMIT: Reg = 27;
const FRAME: Reg = 29;
const LINK: Reg = 30;
/// The closure called, as the call enters it.
const CLO: Reg = 10;
/// From a code bloblet's reference to where its code runs, pinned: the
/// code area's two views are this far apart, less the reference's tag.
const DELTA: Reg = 26;
const X9: Reg = 9;
const X11: Reg = 11;
const X13: Reg = 13;
const X14: Reg = 14;
const X15: Reg = 15;
const X16: Reg = 16;
const X17: Reg = 17;

/// What code in the native convention shares with the Rust side that runs
/// it: where to go back to, the stack's limit, fuel, and what trapped.
#[repr(C)]
#[derive(Default)]
struct DState {
    rust_sp: u64,
    stack_top: u64,
    stack_limit: u64,
    fuel: u64,
    /// The trap's code (`TRAPS`), 0 if none, and where it was raised.
    trap: u64,
    pc: u64,
    args: [u64; 8],
    /// For a call-out: the Rust function, the runtime, the table of what
    /// each call-out is, and the native stack's pointer and frame when it
    /// called out.
    callout: u64,
    rt: u64,
    table: u64,
    native_sp: u64,
    fp: u64,
    /// For allocating inline: where the heap keeps its top (an index), the
    /// address of its word 0, and how far the top may go before a call-out
    /// must allocate (and perhaps collect). A call-out updates the last two.
    top: u64,
    words: u64,
    alloc_limit: u64,
    /// The code bloblet running, kept alive by the call-outs' collections
    /// (it never moves).
    code: u64,
    /// For a call-out that makes a closure: the code bloblet it runs.
    aux: u64,
    /// The closure the call starts in; `DELTA`; and where the code area
    /// starts, below which a closure's code is not native code.
    clo: u64,
    delta: u64,
    code_lo: u64,
}

/// The traps this code raises, by code.
const TRAPS: [&str; 6] =
    ["", "out of fuel", "stack overflow", "integer overflow", "a primitive failed", "a procedure not in the native convention was called"];
const OUT_OF_FUEL: u32 = 1;
const STACK_OVERFLOW: u32 = 2;
const OVERFLOW: u32 = 3;
const PRIM_FAILED: u32 = 4;
const NOT_NATIVE: u32 = 5;

/// What a call-out does: `cons`; a runtime primitive of `n` arguments; a
/// native closure over `n` values of the code in the state's `aux`.
#[derive(Copy, Clone)]
enum Callout {
    Cons,
    Prim { p: usize, n: usize },
    Closure { n: usize },
    /// `%region-closure`'s: in the region whose handle is argument 0, a
    /// native closure over arguments 1 to `n − 2` of the code that is the
    /// last.
    RegionClosure { n: usize },
}

impl Callout {
    fn arity(self) -> usize {
        match self {
            Callout::Cons => 2,
            Callout::Prim { n, .. } | Callout::Closure { n } | Callout::RegionClosure { n } => n,
        }
    }
}

/// What a field of a procedure's code bloblet holds, for its code to read
/// PC-relatively.
#[derive(Clone, PartialEq)]
enum Field {
    /// The bloblet itself, which each frame of it keeps, so that code
    /// running is alive.
    Myself,
    /// Procedure `p`'s code bloblet, which this code calls or makes
    /// closures of.
    Code(usize),
    /// A constant in the heap.
    Const(Value),
    /// A global's cell, read or written when the code runs.
    Cell(Value),
    /// A native closure of procedure `p` over these values: a global's
    /// procedure, used as a value or called, as the global held it when
    /// compiled.
    Closure(usize, Vec<Value>),
}

thread_local! {
    /// Why the last primitive that failed failed.
    static LAST_MESSAGE: std::cell::RefCell<Option<String>> = const { std::cell::RefCell::new(None) };
}

fn st_off(f: usize) -> u32 {
    f as u32
}

/// The native stack: plenty for deep recursion, with room below the limit
/// for the frame that finds it has passed it.
const STACK_WORDS: usize = 1 << 20;
const STACK_SLACK: u64 = 64 * 1024;

#[derive(Copy, Clone)]
struct Label(usize);

/// A branch to a label, made when the label is placed.
#[derive(Copy, Clone)]
enum Fix {
    B,
    Bl,
    If(Cond),
}

/// Instructions with labels, patched when everything is placed.
struct Asm {
    code: Vec<u32>,
    labels: Vec<Option<usize>>,
    fixups: Vec<(usize, Label, Fix)>,
}

impl Asm {
    fn new() -> Asm {
        Asm { code: Vec::new(), labels: Vec::new(), fixups: Vec::new() }
    }
    fn e(&mut self, w: u32) {
        self.code.push(w);
    }
    fn es(&mut self, ws: &[u32]) {
        self.code.extend_from_slice(ws);
    }
    fn label(&mut self) -> Label {
        self.labels.push(None);
        Label(self.labels.len() - 1)
    }
    fn bind(&mut self, l: Label) {
        self.labels[l.0] = Some(self.code.len());
    }
    /// A branch of kind `f` to `l`.
    fn to(&mut self, l: Label, f: Fix) {
        self.fixups.push((self.code.len(), l, f));
        self.code.push(NOP);
    }
    fn finish(mut self) -> Result<Vec<u32>, String> {
        for (at, l, f) in std::mem::take(&mut self.fixups) {
            let to = self.labels[l.0].ok_or("a label never placed")?;
            let d = to as i64 - at as i64;
            self.code[at] = match f {
                Fix::B => b(d),
                Fix::Bl => bl(d),
                Fix::If(c) => b_cond(c, d),
            };
        }
        Ok(self.code)
    }
}

/// A procedure, compiled or being compiled: its cellular word and register
/// word, name and arity, its code bloblet's fields, and its code, of which
/// the first `len` instructions are its own (the rest, its traps').
struct Proc {
    word: Value,
    rw: Value,
    name: String,
    arity: usize,
    fields: Vec<Field>,
    code: Vec<u32>,
    len: usize,
}

/// Compiles procedures and runs them.
pub struct DirectMachine {
    space: CodeSpace,
    /// The trampoline from Rust, and the common trap.
    entry: Offset,
    stack: Vec<u64>,
    /// What each call-out any compiled code makes does, by number.
    callouts: Vec<Callout>,
}

/// A run that trapped: what, and where: the address of the stub its site
/// branched to, one per site.
#[derive(Debug, PartialEq)]
pub struct DirectTrap {
    pub what: String,
    pub pc: u64,
}

/// A compiled procedure: its code bloblet (in the heap's code area), how
/// many instructions are its own, its arity, and a native closure of it
/// over what the closure compiled captured (for the first procedure a
/// compile gives; `#f` for the others). The bloblet lives while something
/// the collector traces refers to it, and while a call runs it; the
/// closure is a heap object, which a collection moves: compile again
/// after one.
#[derive(Copy, Clone, Debug)]
pub struct Compiled {
    pub code: Value,
    pub len: usize,
    pub arity: usize,
    pub closure: Value,
}

impl DirectMachine {
    pub fn new() -> Result<DirectMachine, String> {
        let mut space = CodeSpace::new(8 << 20).map_err(|e| e.to_string())?;
        let code = trampoline();
        let entry = space.alloc(4 * code.len(), 16).ok_or("no room for the trampoline")?;
        space.write_code(entry, &code);
        space.flush(entry, 4 * code.len());
        Ok(DirectMachine { space, entry, stack: vec![0; STACK_WORDS], callouts: Vec::new() })
    }

    /// Compile `closure`'s procedure, and every procedure it calls or
    /// makes closures of, to code in the native convention, each in a code
    /// bloblet of its own: what it compiled, the first first; or why it
    /// could not.
    pub fn compile(&mut self, heap: &mut Heap, closure: Value) -> Result<Vec<(String, Compiled)>, String> {
        let mut c = Compiling { heap: &*heap, procs: Vec::new(), by_word: HashMap::new(), queue: Vec::new(), callouts: &mut self.callouts };
        let (word, free) = c.closure_parts(closure).ok_or("not a closure of cellular code")?;
        let first = c.proc_of(word)?;
        while let Some(p) = c.queue.pop() {
            c.procedure(p)?;
        }
        let procs = std::mem::take(&mut c.procs);
        // Every bloblet first, then their fields, which refer to each other.
        // Nothing here collects, so the values held do not move.
        let blobs: Vec<Value> =
            procs.iter().map(|p| heap.make_code_bloblet(fixpt_heap::layout::kind("bloblet"), p.fields.len(), 4 * p.code.len(), false)).collect();
        for (p, &blob) in procs.iter().zip(&blobs) {
            for (k, f) in p.fields.iter().enumerate() {
                let v = match f {
                    Field::Myself => blob,
                    Field::Code(q) => blobs[*q],
                    Field::Const(v) | Field::Cell(v) => *v,
                    Field::Closure(q, free) => native_closure(heap, blobs[*q], free),
                };
                heap.set_bloblet_slot(blob, k + 1, v);
            }
            let bytes: Vec<u8> = p.code.iter().flat_map(|i| i.to_le_bytes()).collect();
            heap.set_bloblet_bytes(blob, 0, &bytes).map_err(|e| format!("{e:?}"))?;
            heap.flush_code(blob);
        }
        let entry = native_closure(heap, blobs[first], &free);
        Ok(procs
            .iter()
            .zip(&blobs)
            .enumerate()
            .map(|(i, (p, &code))| (p.name.clone(), Compiled { code, len: p.len, arity: p.arity, closure: if i == first { entry } else { Value::FALSE } }))
            .collect())
    }

    /// A native closure, as what it runs: its code, all of it, and the
    /// closure; its arity is not recorded, so a call of it is not checked.
    pub fn compiled_of(heap: &Heap, closure: Value) -> Option<Compiled> {
        if !closure.is_bloblet() || heap.bloblet_kind(closure) != fixpt_heap::layout::kind("native-closure") {
            return None;
        }
        let code = heap.bloblet_slot(closure, CLOSURE_WORD);
        Some(Compiled { code, len: heap.bloblet_head(code).bytes / 4, arity: usize::MAX, closure })
    }

    /// Call `p` with `args`, in at most about `fuel` steps, in `rt`, whose
    /// heap its call-outs allocate in, collecting when they must.
    pub fn call(&mut self, rt: &mut fixpt_runtime::Runtime, p: Compiled, args: &[Value], fuel: u64) -> Result<Value, DirectTrap> {
        assert!(p.arity == usize::MAX || args.len() == p.arity, "the procedure's arity");
        assert!(args.len() <= 8, "arguments in registers only");
        let top = (self.stack.as_mut_ptr() as u64 + 8 * STACK_WORDS as u64) & !15;
        let mut st = DState {
            stack_top: top,
            stack_limit: self.stack.as_ptr() as u64 + STACK_SLACK,
            fuel,
            callout: callout as *const () as u64,
            rt: rt as *mut fixpt_runtime::Runtime as u64,
            table: self.callouts.as_ptr() as u64,
            top: rt.heap.top_address() as u64,
            words: rt.heap.words_address() as u64,
            alloc_limit: rt.heap.inline_limit() as u64,
            ..DState::default()
        };
        for (i, a) in args.iter().enumerate() {
            st.args[i] = a.raw();
        }
        st.code = p.code.raw();
        st.clo = p.closure.raw();
        let target = rt.heap.code_exec_address(p.code) as u64;
        st.delta = target.wrapping_sub(p.code.raw());
        st.code_lo = rt.heap.code_area_address() as u64;
        // SAFETY: the trampoline follows the C convention, saves what it
        // must, runs on the stack in `self.stack` (which outlives the call),
        // and touches only the state and that stack; the procedure's code,
        // compiled above, reads only its arguments and what they point to,
        // in the heap of `rt`, which is exclusively this call's while it
        // runs; it changes only in call-outs, which see every value the
        // native frames hold (`callout`).
        let r = unsafe { self.space.call(self.entry, [&mut st as *mut DState as u64, target, 0, 0]) };
        if st.trap != 0 {
            let what = match LAST_MESSAGE.with(|m| m.borrow_mut().take()) {
                Some(m) if st.trap == PRIM_FAILED as u64 => m,
                _ => TRAPS[st.trap as usize].to_string(),
            };
            return Err(DirectTrap { what, pc: st.pc });
        }
        Ok(Value(r))
    }

    /// `p`'s instructions, as they are in its code bloblet.
    pub fn instructions(&self, heap: &Heap, p: Compiled) -> Vec<u32> {
        let bytes = heap.bloblet_bytes(p.code);
        (0..p.len).map(|i| u32::from_le_bytes(bytes[4 * i..4 * i + 4].try_into().expect("four bytes"))).collect()
    }
}

/// From Rust, `entry(state, procedure)`: the callee-saved registers saved,
/// the native stack entered, the arguments loaded, the procedure called,
/// and back with its value. The common trap follows it: it records the
/// trap and where, and leaves as the trampoline does, through the Rust
/// stack pointer saved in the state.
fn trampoline() -> Vec<u32> {
    let mut a = Asm::new();
    a.e(stp_pre(FRAME, LINK, SP, -96));
    a.e(add_imm(FRAME, SP, 0));
    for (i, r) in [19, 21, 23, 25, 27].iter().enumerate() {
        a.e(stp(*r, *r + 1, SP, 16 + 16 * i as i64));
    }
    a.e(mov(ST, 0));
    a.e(add_imm(X9, SP, 0));
    a.e(str(X9, ST, st_off(offset_of!(DState, rust_sp))));
    a.e(ldr(FUEL, ST, st_off(offset_of!(DState, fuel))));
    a.e(ldr(LIMIT, ST, st_off(offset_of!(DState, stack_limit))));
    a.e(ldr(DELTA, ST, st_off(offset_of!(DState, delta))));
    a.e(ldr(CLO, ST, st_off(offset_of!(DState, clo))));
    a.e(mov(X16, 1));
    a.e(ldr(X9, ST, st_off(offset_of!(DState, stack_top))));
    a.e(add_imm(SP, X9, 0));
    let args = offset_of!(DState, args) as i64;
    for k in 0..4 {
        a.e(ldp(1 + 2 * k, 2 + 2 * k, ST, args + 16 * k as i64));
    }
    a.e(blr(X16));
    a.e(str(FUEL, ST, st_off(offset_of!(DState, fuel))));
    leave(&mut a);
    a.finish().expect("no labels")
}

/// Back to Rust from anywhere on the native stack.
fn leave(a: &mut Asm) {
    a.e(ldr(X9, ST, st_off(offset_of!(DState, rust_sp))));
    a.e(add_imm(SP, X9, 0));
    for (i, r) in [19, 21, 23, 25, 27].iter().enumerate() {
        a.e(ldp(*r, *r + 1, SP, 16 + 16 * i as i64));
    }
    a.e(ldp_post(FRAME, LINK, SP, 96));
    a.e(ret());
}

struct Compiling<'h> {
    heap: &'h Heap,
    procs: Vec<Proc>,
    /// Each procedure's index, by its cellular word.
    by_word: HashMap<u64, usize>,
    /// Those still to compile.
    queue: Vec<usize>,
    /// The machine's call-outs, which this compile adds to.
    callouts: &'h mut Vec<Callout>,
}

impl Compiling<'_> {
    /// The procedure of cellular word `word`, queued to compile if new.
    fn proc_of(&mut self, word: Value) -> Result<usize, String> {
        if let Some(p) = self.by_word.get(&word.raw()) {
            return Ok(*p);
        }
        let h = self.heap;
        let rw = h.bloblet_slot(word, WORD_TWIN);
        if !h.is_register_word(rw) {
            return Err(format!("`{}` has no register code", self.name(word)));
        }
        let arity = h.bloblet_slot(rw, WORD_CELL0 + 1).as_fixnum() as usize;
        let p = self.procs.len();
        self.procs.push(Proc { word, rw, name: self.name(word), arity, fields: vec![Field::Myself], code: Vec::new(), len: 0 });
        self.by_word.insert(word.raw(), p);
        self.queue.push(p);
        Ok(p)
    }

    fn name(&self, word: Value) -> String {
        self.heap.symbol_name(self.heap.bloblet_slot(word, fixpt_heap::layout::cellular::WORD_NAME))
    }

    /// A cellular closure's procedure and free values; `None` for anything
    /// else.
    fn closure_parts(&self, v: Value) -> Option<(Value, Vec<Value>)> {
        let h = self.heap;
        if !v.is_bloblet() || h.bloblet_kind(v) != fixpt_heap::layout::kind("cellular-closure") {
            return None;
        }
        let fields = h.bloblet_head(v).fields;
        Some((h.bloblet_slot(v, CLOSURE_WORD), (CLOSURE_FREE0..=fields).map(|k| h.bloblet_slot(v, k)).collect()))
    }

    /// Procedure `p`'s field holding `f`: an index from 1, shared with an
    /// equal one.
    fn field(&mut self, p: usize, f: Field) -> usize {
        let fs = &mut self.procs[p].fields;
        match fs.iter().position(|g| *g == f) {
            Some(k) => k + 1,
            None => {
                fs.push(f);
                fs.len()
            }
        }
    }

    /// How a global's value is had: the global's cell, read when the code
    /// runs, as Larceny's code reads its globals, so that a later
    /// definition is seen; but a cellular closure (a procedure the cellular
    /// machine made), which native code cannot call, is compiled and bound
    /// now, as a native closure of its procedure.
    fn global_value(&mut self, cell: Value) -> Result<Field, String> {
        let v = self.heap.bloblet_slot(cell, 2);
        // Not defined yet (a definition of itself, being compiled): what its
        // cell holds when the code runs.
        if let Some((word, free)) = self.closure_parts(v)
            && self.name(word) != "undefined"
        {
            let q = self.proc_of(word)?;
            return Ok(match free.is_empty() {
                true => Field::Code(q),
                false => Field::Closure(q, free),
            });
        }
        Ok(Field::Cell(cell))
    }

    /// One procedure's code, from its register word.
    fn procedure(&mut self, p: usize) -> Result<(), String> {
        let h = self.heap;
        let (word, rw) = (self.procs[p].word, self.procs[p].rw);
        let fields = h.bloblet_head(rw).fields;
        let cells: Vec<Value> = (WORD_CELL0..=fields).map(|k| h.bloblet_slot(rw, k)).collect();
        let name = self.name(word);
        let decline = |what: String| Err(format!("`{name}`: {what}"));
        // Where each instruction starts, what a branch goes back to, and
        // whether the procedure has a frame, calls, or reads its closure.
        let mut starts = Vec::new();
        let mut back_to = vec![false; cells.len() + 1];
        let mut target = vec![false; cells.len() + 1];
        let (mut frame, mut calls, mut captures) = (None, false, false);
        let mut i = 0;
        while i < cells.len() {
            starts.push(i);
            let (op, n, _) = OPS[cells[i].as_fixnum() as usize];
            match op {
                "branch" | "branchf" => {
                    let to = i as i64 + 2 + cells[i + 1].as_fixnum();
                    target[to as usize] = true;
                    if to <= i as i64 {
                        back_to[to as usize] = true;
                    }
                }
                "save" => frame = Some(cells[i + 1].as_fixnum() as usize),
                "invoke" | "tailinvoke" | "invokeself" => calls = true,
                "lexical" => captures = true,
                _ => {}
            }
            i += 1 + n;
        }
        let op_at = |j: usize| OPS[cells[j].as_fixnum() as usize].0;
        // What each `global` is for: a call just after it (a tail call's
        // frame popped between), or its value.
        let called = |j: usize| {
            let at = starts.iter().position(|&s| s == j).expect("an instruction");
            starts[at + 1..].iter().copied().find(|&c| op_at(c) != "pop").filter(|&c| matches!(op_at(c), "invoke" | "tailinvoke"))
        };
        // The frame: the link and return address, register code's slots,
        // then this code bloblet and the closure running.
        if frame.is_some_and(|m| 16 + 8 * (m + 2) > 504) {
            return decline("a frame too large for one `stp`".into());
        }
        let size = frame.map(|m| (16 + 8 * (m as u32 + 2)).div_ceil(16) * 16);
        let self_slot = frame.map(|m| 16 + 8 * m as u32);
        let clo_slot = frame.map(|m| 16 + 8 * (m as u32 + 1));
        let mut a = Asm::new();
        let entry = a.label();
        let labels: Vec<Label> = (0..=cells.len()).map(|_| a.label()).collect();
        // Each trap site branches to a stub of its own, which calls the
        // trap's code: so the return address says where it was.
        let mut stubs: Vec<(Label, u32)> = Vec::new();
        let trap = |a: &mut Asm, stubs: &mut Vec<(Label, u32)>, code: u32, c: Cond| {
            let l = a.label();
            stubs.push((l, code));
            a.to(l, Fix::If(c));
        };
        a.bind(entry);
        if calls || frame.is_some() {
            a.e(subs_imm(FUEL, FUEL, 1));
            trap(&mut a, &mut stubs, OUT_OF_FUEL, Cond::Lo);
        }
        let sets_first = |j: usize| matches!(op_at(j), "const" | "reg" | "stack" | "global" | "lexical");
        let ignores = |j: usize| sets_first(j) || matches!(op_at(j), "invokeself");
        let joinable = |si: usize| starts.get(si + 1).copied().filter(|&j| !target[j]);
        let mut src = RESULT;
        // A global about to be called: the call to make.
        let mut pending: Option<Field> = None;
        let mut si = 0;
        while si < starts.len() {
            let i = starts[si];
            si += 1;
            a.bind(labels[i]);
            let op = op_at(i);
            let o = |j: usize| cells[i + 1 + j];
            let k = |v: Value| v.as_fixnum() as usize;
            let reg = |v: Value| v.as_fixnum() as Reg;
            match op {
                "args" => {}
                "const" => {
                    let v = o(0);
                    if v.is_fixnum() || v.raw() & 7 == 3 {
                        a.es(&mov_imm64(RESULT, v.raw()));
                    } else if h.is_cellular_word(v) {
                        // A word, which only a closure is made of: its code
                        // here, compiled, in its place.
                        let q = self.proc_of(v).map_err(|e| format!("`{name}` makes a closure of {e}"))?;
                        let f = self.field(p, Field::Code(q));
                        ldr_field(&mut a, RESULT, f);
                    } else {
                        let f = self.field(p, Field::Const(v));
                        ldr_field(&mut a, RESULT, f);
                    }
                }
                "global" => {
                    let cell = o(0);
                    let g = self.global_value(cell).map_err(|e| format!("`{name}` calls {e}"))?;
                    if called(i).is_some() {
                        pending = Some(g);
                    } else {
                        match g {
                            Field::Cell(c) => {
                                let f = self.field(p, Field::Cell(c));
                                ldr_field(&mut a, X9, f);
                                a.e(ldur(RESULT, X9, field_off(2)));
                            }
                            // A procedure's code alone is no value: its
                            // closure, over nothing.
                            Field::Code(q) => {
                                let f = self.field(p, Field::Closure(q, vec![]));
                                ldr_field(&mut a, RESULT, f);
                            }
                            g => {
                                let f = self.field(p, g);
                                ldr_field(&mut a, RESULT, f);
                            }
                        }
                    }
                }
                "setglbl" => {
                    let f = self.field(p, Field::Cell(o(0)));
                    ldr_field(&mut a, X9, f);
                    a.e(stur(RESULT, X9, field_off(2)));
                }
                "lexical" => {
                    let from = match clo_slot {
                        Some(s) => {
                            a.e(ldr(X9, FRAME, s));
                            X9
                        }
                        None => CLO,
                    };
                    let off = field_off(CLOSURE_FREE0 + k(o(0)));
                    if off < -256 {
                        return decline("a closure too large".into());
                    }
                    a.e(ldur(RESULT, from, off));
                }
                "reg" => match joinable(si - 1) {
                    Some(j) if matches!(op_at(j), "op2" | "op2imm") => {
                        src = reg(o(0));
                        continue;
                    }
                    _ => a.e(mov(RESULT, reg(o(0)))),
                },
                "setreg" => a.e(mov(reg(o(0)), RESULT)),
                "movereg" => a.e(mov(reg(o(1)), reg(o(0)))),
                // The frame made: the stack's limit checked (it leaves room
                // for any one frame below it); every slot a value from the
                // start, the fixnum 0, so that a collection may scan the
                // whole frame; this code bloblet in its slot, so that the
                // frame keeps it alive; the closure in its, if the code
                // reads it.
                "save" => {
                    let size = size.expect("a frame") as i64;
                    a.e(stp_pre(FRAME, LINK, SP, -size));
                    a.e(add_imm(FRAME, SP, 0));
                    a.e(cmp_sp(LIMIT));
                    trap(&mut a, &mut stubs, STACK_OVERFLOW, Cond::Lo);
                    for off in (16..size).step_by(16) {
                        a.e(stp(XZR, XZR, FRAME, off));
                    }
                    ldr_field(&mut a, X9, 1);
                    a.e(str(X9, FRAME, self_slot.expect("a frame")));
                    if captures {
                        a.e(str(CLO, FRAME, clo_slot.expect("a frame")));
                    }
                }
                "pop" => a.e(ldp_post(FRAME, LINK, SP, size.expect("a frame") as i64)),
                "stack" => a.e(ldr(RESULT, FRAME, 16 + 8 * k(o(0)) as u32)),
                "setstk" => a.e(str(RESULT, FRAME, 16 + 8 * k(o(0)) as u32)),
                "load" => a.e(ldr(reg(o(0)), FRAME, 16 + 8 * k(o(1)) as u32)),
                "store" => {
                    a.e(str(reg(o(0)), FRAME, 16 + 8 * k(o(1)) as u32));
                    // Its slot read back at once: the register is still it.
                    if let Some(j) = joinable(si - 1)
                        && op_at(j) == "stack"
                        && cells[j + 1] == o(1)
                    {
                        a.bind(labels[j]);
                        si += 1;
                        match joinable(si - 1) {
                            Some(n) if matches!(op_at(n), "op2" | "op2imm") => src = reg(o(0)),
                            _ => a.e(mov(RESULT, reg(o(0)))),
                        }
                    }
                }
                "op1" => match ROUTINES[k(o(0))].0 {
                    "pair-car" => a.e(ldur(RESULT, RESULT, -1)),
                    "pair-cdr" => a.e(ldur(RESULT, RESULT, 7)),
                    r => return decline(format!("op1 {r}")),
                },
                "op2" | "op2imm" => {
                    let x = std::mem::replace(&mut src, RESULT);
                    // The other operand: a register, or a constant, which an
                    // add, a subtract or a compare may take as it is when it
                    // is small.
                    let (other, small) = if op == "op2" {
                        (reg(o(1)), None)
                    } else {
                        let v = o(1);
                        if !(v.is_fixnum() || v.raw() & 7 == 3) {
                            let f = self.field(p, Field::Const(v));
                            ldr_field(&mut a, X16, f);
                            (X16, None)
                        } else if v.raw() < 4096 {
                            (X16, Some(v.raw() as u32))
                        } else {
                            a.es(&mov_imm64(X16, v.raw()));
                            (X16, None)
                        }
                    };
                    let r = ROUTINES[k(o(0))].0;
                    // A sum or difference only moved on to a register, and
                    // then not read: made in that register.
                    let mut d = RESULT;
                    if matches!(r, "int-add" | "int-sub")
                        && let Some(j) = joinable(si - 1)
                        && op_at(j) == "setreg"
                        && starts.get(si + 1).is_some_and(|&f| ignores(f))
                    {
                        a.bind(labels[j]);
                        d = reg(cells[j + 1]);
                        si += 1;
                    }
                    match (r, small) {
                        ("int-add", Some(n)) => a.e(adds_imm(d, x, n)),
                        ("int-add", None) => a.e(adds(d, x, other)),
                        ("int-sub", Some(n)) => a.e(subs_imm(d, x, n)),
                        ("int-sub", None) => a.e(subs(d, x, other)),
                        ("int-less" | "eq", Some(n)) => a.e(cmp_imm(x, n)),
                        ("int-less" | "eq", None) => a.e(cmp(x, other)),
                        _ => return decline(format!("{op} {r}")),
                    }
                    let cond = if r == "eq" { Cond::Eq } else { Cond::Lt };
                    match r {
                        "int-add" | "int-sub" => trap(&mut a, &mut stubs, OVERFLOW, Cond::Vs),
                        // A test that only a branch reads: the branch on the
                        // flags, with no boolean made.
                        _ => match joinable(si - 1) {
                            Some(j)
                                if op_at(j) == "branchf"
                                    && starts.get(si + 1).is_none_or(|&f| sets_first(f))
                                    && sets_first((j as i64 + 2 + cells[j + 1].as_fixnum()) as usize) =>
                            {
                                a.bind(labels[j]);
                                let to = (j as i64 + 2 + cells[j + 1].as_fixnum()) as usize;
                                a.to(labels[to], Fix::If(if r == "eq" { Cond::Ne } else { Cond::Ge }));
                                si += 1;
                            }
                            _ => {
                                a.es(&mov_imm64(X9, Value::TRUE.raw()));
                                a.es(&mov_imm64(X17, Value::FALSE.raw()));
                                a.e(csel(RESULT, X9, X17, cond));
                            }
                        },
                    }
                }
                "field" => {
                    let off = field_off(k(o(0)));
                    if off < -256 {
                        return decline("a field too far".into());
                    }
                    a.e(ldur(RESULT, RESULT, off));
                }
                "setfield" => {
                    let off = field_off(k(o(0)));
                    if off < -256 {
                        return decline("a field too far".into());
                    }
                    a.e(stur(reg(o(1)), RESULT, off));
                }
                // A call-out: to Rust, on Rust's stack, which may collect;
                // everything live is in the frame by then (register code
                // sees to it), and the arguments go through the state.
                "prim" | "cellular" | "lambda" => {
                    let c = match (op, ROUTINES.get(k(o(0))).map(|r| r.0)) {
                        ("lambda", _) => {
                            let q = self.proc_of(o(0)).map_err(|e| format!("`{name}` makes a closure of {e}"))?;
                            let f = self.field(p, Field::Code(q));
                            ldr_field(&mut a, X9, f);
                            a.e(str(X9, ST, st_off(offset_of!(DState, aux))));
                            Callout::Closure { n: k(o(1)) }
                        }
                        ("cellular", Some("cons")) if k(o(1)) == 2 => Callout::Cons,
                        ("prim", _) => match fixpt_runtime::PRIMITIVES.get(k(o(0))) {
                            Some(d) if d.name == "%region-closure" => Callout::RegionClosure { n: k(o(1)) },
                            Some(d) if matches!(d.kind, fixpt_runtime::PrimKind::Simple(_)) && d.accepts(k(o(1))) => {
                                Callout::Prim { p: k(o(0)), n: k(o(1)) }
                            }
                            Some(d) => return decline(format!("the primitive `{}`", d.name)),
                            None => return decline(format!("primitive {}", k(o(0)))),
                        },
                        (_, r) => return decline(format!("the routine `{}`", r.unwrap_or("?"))),
                    };
                    if frame.is_none() {
                        return decline("a call-out outside a frame".into());
                    }
                    // A pair, from the heap's free space when there is room
                    // short of the collection's threshold; else the call-out.
                    let done = a.label();
                    let slow = a.label();
                    if let Callout::Cons = c {
                        a.e(ldr(X13, ST, st_off(offset_of!(DState, top))));
                        a.e(ldr(X14, X13, 0));
                        a.e(ldr(X15, ST, st_off(offset_of!(DState, alloc_limit))));
                        a.e(add_imm(X16, X14, 2));
                        a.e(cmp(X16, X15));
                        a.to(slow, Fix::If(Cond::Hi));
                        a.e(ldr(X9, ST, st_off(offset_of!(DState, words))));
                        a.e(add_lsl(X11, X9, X14, 3));
                        a.e(stp(1, 2, X11, 0));
                        a.e(str(X16, X13, 0));
                        a.e(add_imm(RESULT, X11, fixpt_heap::value::TAG_PAIR as u32));
                        a.to(done, Fix::B);
                    }
                    a.bind(slow);
                    let n = self.callouts.len();
                    self.callouts.push(c);
                    let args = offset_of!(DState, args) as u32;
                    for j in 0..c.arity() {
                        a.e(str(1 + j as Reg, ST, args + 8 * j as u32));
                    }
                    a.e(str(FRAME, ST, st_off(offset_of!(DState, fp))));
                    a.e(add_imm(X9, SP, 0));
                    a.e(str(X9, ST, st_off(offset_of!(DState, native_sp))));
                    a.e(ldr(X9, ST, st_off(offset_of!(DState, rust_sp))));
                    a.e(add_imm(SP, X9, 0));
                    a.e(mov(0, ST));
                    a.es(&mov_imm64(1, n as u64));
                    a.e(ldr(X16, ST, st_off(offset_of!(DState, callout))));
                    a.e(blr(X16));
                    a.e(ldr(X9, ST, st_off(offset_of!(DState, native_sp))));
                    a.e(add_imm(SP, X9, 0));
                    a.e(ldr(X9, ST, st_off(offset_of!(DState, trap))));
                    a.e(cmp_imm(X9, 0));
                    trap(&mut a, &mut stubs, PRIM_FAILED, Cond::Ne);
                    a.bind(done);
                }
                // A call. Of a global's procedure that captures nothing: its
                // code, from this bloblet's field, entered at its start. Of
                // any other procedure: a native closure, in `CLO`, whose
                // field 2 is its code, entered so; one whose field 2 is not
                // in the code area is not native code, and traps.
                "invoke" | "tailinvoke" => {
                    let tail = op == "tailinvoke";
                    match pending.take() {
                        Some(Field::Code(q)) => {
                            let f = self.field(p, Field::Code(q));
                            ldr_field(&mut a, X16, f);
                        }
                        // Through the global's cell, when the code runs: what
                        // it holds then, which must be native code.
                        Some(Field::Cell(c)) => {
                            let f = self.field(p, Field::Cell(c));
                            ldr_field(&mut a, X9, f);
                            a.e(ldur(CLO, X9, field_off(2)));
                            a.e(ldur(X16, CLO, field_off(CLOSURE_WORD)));
                            a.e(ldr(X17, ST, st_off(offset_of!(DState, code_lo))));
                            a.e(cmp(X16, X17));
                            trap(&mut a, &mut stubs, NOT_NATIVE, Cond::Lo);
                        }
                        Some(g) => {
                            let f = self.field(p, g);
                            ldr_field(&mut a, CLO, f);
                            a.e(ldur(X16, CLO, field_off(CLOSURE_WORD)));
                        }
                        None => {
                            a.e(mov(CLO, RESULT));
                            a.e(ldur(X16, CLO, field_off(CLOSURE_WORD)));
                            a.e(ldr(X17, ST, st_off(offset_of!(DState, code_lo))));
                            a.e(cmp(X16, X17));
                            trap(&mut a, &mut stubs, NOT_NATIVE, Cond::Lo);
                        }
                    }
                    a.e(add(X16, X16, DELTA));
                    a.e(if tail { br(X16) } else { blr(X16) });
                }
                "invokeself" => {
                    if let Some(s) = clo_slot.filter(|_| captures) {
                        a.e(ldr(CLO, FRAME, s));
                    }
                    a.to(entry, Fix::Bl);
                }
                "return" => a.e(ret()),
                "branch" | "branchf" => {
                    let to = (i as i64 + 2 + o(0).as_fixnum()) as usize;
                    if op == "branchf" {
                        a.es(&mov_imm64(X16, Value::FALSE.raw()));
                        a.e(cmp(RESULT, X16));
                        a.to(labels[to], Fix::If(Cond::Eq));
                    } else {
                        if back_to[to] {
                            a.e(subs_imm(FUEL, FUEL, 1));
                            trap(&mut a, &mut stubs, OUT_OF_FUEL, Cond::Lo);
                        }
                        a.to(labels[to], Fix::B);
                    }
                }
                other => return decline(format!("`{other}`")),
            }
        }
        a.bind(labels[cells.len()]);
        // The traps, out of the way: a stub per site, calling its kind's
        // code, which records the trap and where, and leaves.
        let kinds: Vec<Label> = (0..TRAPS.len()).map(|_| a.label()).collect();
        for (l, code) in &stubs {
            a.bind(*l);
            a.to(kinds[*code as usize], Fix::Bl);
        }
        for (code, l) in kinds.iter().enumerate().skip(1) {
            if !stubs.iter().any(|(_, c)| *c as usize == code) {
                continue;
            }
            a.bind(*l);
            a.e(movz(X9, code as u32, 0));
            a.e(str(X9, ST, st_off(offset_of!(DState, trap))));
            a.e(sub_imm(X9, LINK, 4));
            a.e(str(X9, ST, st_off(offset_of!(DState, pc))));
            a.e(str(FUEL, ST, st_off(offset_of!(DState, fuel))));
            leave(&mut a);
        }
        let len = stubs.first().map_or(a.code.len(), |(l, _)| a.labels[l.0].expect("placed"));
        self.procs[p].code = a.finish()?;
        self.procs[p].len = len;
        Ok(())
    }
}

/// `t` := field `k` of the code bloblet being made, PC-relatively: field
/// `k` is `8k` bytes before the code's first instruction.
fn ldr_field(a: &mut Asm, t: Reg, k: usize) {
    let at = a.code.len() as i64;
    a.e(ldr_lit(t, -2 * k as i64 - at));
}

/// Field `k` of the bloblet whose `suffix + 4` is in a register, as an
/// offset from that register.
fn field_off(k: usize) -> i64 {
    -(4 + 8 * k as i64)
}

/// A call-out from native code: call-out number `which`, its arguments in
/// the state. Collects first if it must, with every value in the native
/// frames a root, and those in the frames updated. Returns the value made,
/// or sets a trap.
extern "C" fn callout(st: *mut DState, which: u64) -> u64 {
    // SAFETY: `st` is the state `DirectMachine::call` made, alive for the
    // whole call; its `rt` is the runtime that call holds exclusively; its
    // `table`, the machine's call-outs, which do not change while it runs.
    let st = unsafe { &mut *st };
    let rt = unsafe { &mut *(st.rt as *mut fixpt_runtime::Runtime) };
    let c = unsafe { *(st.table as *const Callout).add(which as usize) };
    let mut args: Vec<Value> = st.args[..c.arity()].iter().map(|a| Value(*a)).collect();
    let mut code = [Value(st.code)];
    {
        let mut roots = native_frames(st);
        roots.push(&mut args);
        roots.push(&mut code);
        rt.heap.maybe_collect(&mut roots);
    }
    let out = match c {
        Callout::Cons => rt.heap.cons(args[0], args[1]).raw(),
        Callout::Closure { .. } => native_closure(&mut rt.heap, Value(st.aux), &args).raw(),
        Callout::RegionClosure { n } => {
            let h = if args[0].is_fixnum() { args[0].as_fixnum() as usize } else { usize::MAX };
            let (free, code) = (&args[1..n - 1], args[n - 1]);
            rt.heap.in_region(h, |heap| native_closure(heap, code, free)).raw()
        }
        Callout::Prim { p, .. } => {
            let def = &fixpt_runtime::PRIMITIVES[p];
            let fixpt_runtime::PrimKind::Simple(f) = def.kind else { unreachable!("checked when compiled") };
            match f(rt, &mut args) {
                Ok(v) => v.raw(),
                Err(t) => {
                    let m = fixpt_engine::cellular::describe(rt, t.obj);
                    LAST_MESSAGE.with(|c| *c.borrow_mut() = Some(m));
                    st.trap = PRIM_FAILED as u64;
                    0
                }
            }
        }
    };
    // Where the heap is now, and how far native code may allocate in it.
    st.words = rt.heap.words_address() as u64;
    st.alloc_limit = rt.heap.inline_limit() as u64;
    out
}

/// The slots of every native frame, innermost first, from the frame that
/// called out: each frame runs from its frame pointer to its caller's, the
/// outermost to the stack's top, and every word of it but the first two
/// (the caller's frame pointer and the return address) is a value.
fn native_frames<'a>(st: &DState) -> Vec<&'a mut [Value]> {
    let mut out = Vec::new();
    let mut fp = st.fp;
    while fp != 0 && fp < st.stack_top {
        // SAFETY: a frame on the native stack, made by `save`, whose first
        // word is the caller's frame pointer.
        let caller = unsafe { *(fp as *const u64) };
        let end = if caller > fp && caller <= st.stack_top { caller } else { st.stack_top };
        let n = ((end - fp) / 8) as usize - 2;
        // SAFETY: the frame's slots, each a value (`save` zeroes them), not
        // overlapping any other frame's.
        out.push(unsafe { std::slice::from_raw_parts_mut((fp + 16) as *mut Value, n) });
        fp = if end == caller { caller } else { 0 };
    }
    out
}

/// A native closure of the code in code bloblet `code`, over `free`.
fn native_closure(heap: &mut Heap, code: Value, free: &[Value]) -> Value {
    let c = heap.make_bloblet(fixpt_heap::layout::kind("native-closure"), free.len() + 1, 0, true);
    heap.set_bloblet_slot(c, CLOSURE_WORD, code);
    for (i, v) in free.iter().enumerate() {
        heap.set_bloblet_slot(c, CLOSURE_FREE0 + i, *v);
    }
    c
}

/// A native closure's code, shown: what it captured, its instructions one
/// to a line, and those of every procedure it reaches through its code
/// bloblet's fields, each once. For `%disassemble` (`Runtime::native_code`).
pub fn code_text(heap: &Heap, closure: Value) -> Option<String> {
    use std::fmt::Write as _;
    if !closure.is_bloblet() || heap.bloblet_kind(closure) != fixpt_heap::layout::kind("native-closure") {
        return None;
    }
    let mut out = String::new();
    let free = (heap.bloblet_head(closure).fields + 1).saturating_sub(CLOSURE_FREE0);
    let _ = writeln!(out, "a native closure over {free} value(s):");
    for i in 0..free {
        let _ = writeln!(out, "  free {i}: {}", fixpt_runtime::write_value(heap, heap.bloblet_slot(closure, CLOSURE_FREE0 + i)));
    }
    let (mut todo, mut seen) = (vec![heap.bloblet_slot(closure, CLOSURE_WORD)], Vec::new());
    while let Some(code) = todo.pop() {
        if seen.contains(&code.raw()) || !heap.is_code_bloblet(code) {
            continue;
        }
        seen.push(code.raw());
        let bytes = heap.bloblet_bytes(code);
        let _ = writeln!(out, "\ncode {}, {} instructions:", seen.len(), bytes.len() / 4);
        for (i, w) in bytes.chunks_exact(4).enumerate() {
            let w = u32::from_le_bytes(w.try_into().expect("four bytes"));
            let _ = writeln!(out, "  {i:>4}  {}", crate::arm64::disasm::disassemble(w, i as i64));
        }
        // What it calls, and makes closures of: code in its fields, and
        // in the closures there.
        for k in 1..=heap.bloblet_head(code).fields {
            let f = heap.bloblet_slot(code, k);
            if heap.is_code_bloblet(f) {
                todo.push(f);
            } else if f.is_bloblet() && heap.bloblet_kind(f) == fixpt_heap::layout::kind("native-closure") {
                todo.push(heap.bloblet_slot(f, CLOSURE_WORD));
            }
        }
    }
    Some(out)
}

