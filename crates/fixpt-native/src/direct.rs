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
//! | values across a call | the frame's slots, `[x29, #24 + 8n]` for slot `n`          |
//! | the frame's stack map | `[x29, #16]`: a fixnum, the mask of the slots traced       |
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
    /// For a call-out that makes a closure: the code bloblet it runs; for
    /// one that calls what is not native code, that, and how many
    /// arguments it is given.
    aux: u64,
    nargs: u64,
    /// The closure the call starts in; `DELTA`; and where the code area
    /// starts, below which a closure's code is not native code.
    clo: u64,
    delta: u64,
    code_lo: u64,
    /// For control: where a continuation taken now resumes (set by the code
    /// before the call-out that takes it); where a call-out that does not
    /// return to its caller goes instead (the stack, frame, code and value
    /// it resumes with); and how many regions are live, as a fixnum, which
    /// a prompt keeps.
    ret_pc: u64,
    resume_sp: u64,
    resume_fp: u64,
    resume_pc: u64,
    resume_x0: u64,
    regions: u64,
    /// The machine's `mark_ret`, where it runs.
    mark_ret: u64,
    /// The machine's common trap, where it runs: a code's stub for a kind
    /// of trap puts the kind in X9 and goes there, the return address still
    /// the site's.
    trap_stub: u64,
    /// The machine's common call of what is not native code
    /// (`common_foreign`), where it runs.
    foreign: u64,
    /// The machine's common making of a closure by call-out
    /// (`common_closure`), where it runs.
    closure: u64,
}

/// The traps this code raises, by code.
const TRAPS: [&str; 5] = ["", "out of fuel", "stack overflow", "integer overflow", "a primitive failed"];
const OUT_OF_FUEL: u32 = 1;
const STACK_OVERFLOW: u32 = 2;
const OVERFLOW: u32 = 3;
const PRIM_FAILED: u32 = 4;

/// What a call-out does: `cons`; a runtime primitive of `n` arguments; a
/// native closure over `n` values of the code in the state's `aux`.
#[derive(Copy, Clone)]
enum Callout {
    Cons,
    Prim { p: usize, n: usize },
    Closure { n: usize },
    /// The same, over the state's `nargs` values: the machine's common
    /// routine's (`common_closure`), for a closure the inline path had no
    /// room for.
    ClosureAny,
    /// `%region-closure`'s: in the region whose handle is argument 0, a
    /// native closure over arguments 1 to `n − 2` of the code that is the
    /// last.
    RegionClosure { n: usize },
    /// `field@`: field `k` (argument 1) of the bloblet that is argument 0,
    /// when the inline path found it out of range or not a bloblet.
    FieldRef,
    /// A call of what is not native code, in the state's `aux`, with the
    /// state's `nargs` arguments: a cellular closure or continuation, run
    /// by the cellular machine (`fixpt_engine::cellular::call_value`).
    Foreign,
    /// `abort-current-continuation`: to the innermost prompt for the tag
    /// (argument 0), with the value (argument 1), resumed at its landing.
    Abort,
    /// A continuation taken, whole (`cwcc`) or up to the innermost prompt
    /// for the tag (argument 1): a native closure over the frames it takes,
    /// of the code in the state's `aux`, the continuation procedure.
    Capture { whole: bool },
    /// A continuation (argument 1) given a value (argument 0): its frames
    /// put back, and resumed.
    Reinstate,
    /// `first-mark`: the innermost mark for the key, or the default.
    FirstMark,
    /// `current-marks`: every mark for the key, innermost first.
    CurrentMarks,
    /// `marks-of`: those a continuation took.
    MarksOf,
}

impl Callout {
    fn arity(self) -> usize {
        match self {
            Callout::Cons | Callout::FieldRef | Callout::Abort | Callout::Reinstate | Callout::FirstMark | Callout::MarksOf => 2,
            Callout::Capture { whole } => if whole { 1 } else { 2 },
            Callout::CurrentMarks => 1,
            Callout::Foreign | Callout::ClosureAny => 0,
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
    // Field 2 is always `Const` of the cellular word compiled
    // (`layout::cellular::CODE_SOURCE`), for `,disassemble` to show.
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
    /// This thread's machine, made when first asked for: the one every
    /// native closure its code makes runs on, since that code's call-outs
    /// are numbered in its table.
    static MACHINE: std::cell::RefCell<Option<DirectMachine>> = const { std::cell::RefCell::new(None) };
    /// A whole continuation of cellular code, and its value, thrown past
    /// the native code running: the call traps, and the caller throws it on.
    static THROWN: std::cell::Cell<Option<(Value, Value)>> = const { std::cell::Cell::new(None) };
    /// While native code has called out to run cellular code: how to run
    /// native code, and the native stack's pointer as it called out, below
    /// which a native call from that cellular code runs (`call_native`),
    /// the machine being in use.
    static CALLED_OUT: std::cell::Cell<Option<(Runner, u64)>> = const { std::cell::Cell::new(None) };
    /// The run of native code innermost, if one is running.
    static RUNNING: std::cell::Cell<Option<Runner>> = const { std::cell::Cell::new(None) };
}

/// What a run of native code needs of its machine: where the trampoline,
/// stubs and call-outs' table are, and the stack's lowest address.
#[derive(Clone, Copy)]
struct Runner {
    entry: u64,
    mark_ret: u64,
    trap_stub: u64,
    foreign: u64,
    closure: u64,
    table: u64,
    stack_lo: u64,
}

/// The continuation, and its value, that the last call that trapped threw
/// past its native code, if it did.
pub fn take_thrown() -> Option<(Value, Value)> {
    THROWN.with(|t| t.take())
}

/// `f` of this thread's machine; or why not: no code space for one, or it
/// is running already (a native call from code a native call called, which
/// cannot be yet).
pub fn with_machine<T>(f: impl FnOnce(&mut DirectMachine) -> T) -> Result<T, String> {
    MACHINE.with(|m| {
        let mut m = m.try_borrow_mut().map_err(|_| "native code called from code native code called".to_string())?;
        if m.is_none() {
            *m = Some(DirectMachine::new()?);
        }
        Ok(f(m.as_mut().expect("made")))
    })
}

/// A cellular closure compiled on this thread's machine: a native closure
/// of the same code over the same values, or why not.
pub fn compile_closure(heap: &mut Heap, closure: Value) -> Result<Value, String> {
    with_machine(|m| m.compile(heap, closure).map(|procs| procs[0].1.closure))?
}

/// A runtime's `adapt` (`%fx26-convert`): an adapter of `f`, of `arity`
/// arguments, to the native convention if `native`, else to the cellular
/// one. To the native convention, a native closure over `f` whose code
/// calls it as native code calls what is not native code, through the
/// machine's `common_foreign`, in a tail call:
///
/// ```text
/// ldur x10, [x10, #free 0]    the closure called: now `f`
/// movz x9, #arity
/// ldr  x16, [x24, #foreign]
/// br   x16
/// ```
pub fn adapt(rt: &mut fixpt_runtime::Runtime, f: Value, arity: usize, native: bool) -> Result<Value, String> {
    let heap = &mut rt.heap;
    if !native {
        return Ok(fixpt_engine::cellular::cellular_adapter(heap, f, arity));
    }
    if arity > 8 {
        return Err("an adapter to the native convention of more than 8 arguments".into());
    }
    let mut a = Asm::new();
    a.e(ldur(CLO, CLO, field_off(CLOSURE_FREE0)));
    a.e(movz(X9, arity as u32, 0));
    a.e(ldr(X16, ST, st_off(offset_of!(DState, foreign))));
    a.e(br(X16));
    let code = a.finish().expect("no labels");
    let blob = heap.make_code_bloblet(fixpt_heap::layout::kind("bloblet"), 1, 4 * code.len(), false);
    heap.set_bloblet_slot(blob, 1, blob);
    let bytes: Vec<u8> = code.iter().flat_map(|i| i.to_le_bytes()).collect();
    heap.set_bloblet_bytes(blob, 0, &bytes).map_err(|e| format!("{e:?}"))?;
    heap.flush_code(blob);
    Ok(native_closure(heap, blob, &[f]))
}

/// A runtime's `call_native`: native closure `closure` called with `args`
/// on this thread's machine, in the steps a word may take.
///
/// Called from cellular code that native code called, the machine is in
/// use: the call runs on its stack below the frames of the run that called
/// out, whose values that call-out keeps rooted.
pub fn call_native(rt: &mut fixpt_runtime::Runtime, closure: Value, args: &[Value]) -> Result<Value, fixpt_runtime::NativeExit> {
    let fail = fixpt_runtime::NativeExit::Failed;
    let p = DirectMachine::compiled_of(&rt.heap, closure).ok_or_else(|| fail("not a native closure".into()))?;
    if args.len() > 8 {
        return Err(fail("a native call of more than 8 arguments".into()));
    }
    let fuel = rt.word_fuel.min(u64::MAX >> 1);
    let r = match CALLED_OUT.with(|c| c.get()) {
        Some((runner, sp)) => {
            let top = (sp - 16) & !15;
            if top < runner.stack_lo + 2 * STACK_SLACK {
                return Err(fail("stack overflow".into()));
            }
            run(&runner, rt, p, args, fuel, top)
        }
        None => with_machine(|m| m.call(rt, p, args, fuel)).map_err(fail)?,
    };
    r.map_err(|t| match take_thrown() {
        Some((k, v)) => fixpt_runtime::NativeExit::Throw { k, v },
        None => fail(t.what),
    })
}

/// What a prompt's frame, and a mark's, holds first, and a continuation's
/// data: values no program can make (`UNBOUND` with a payload), so no other
/// frame's first slot is one.
const PROMPT_MARK: Value = Value(Value::UNBOUND.raw() + (1 << 8));
const MARK_MARK: Value = Value(Value::UNBOUND.raw() + (2 << 8));
const CONT_MARK: Value = fixpt_heap::NATIVE_CONT_MARK;
/// A prompt's frame, and a mark's: the link, the landing (for a mark, 0),
/// the marker, the tag and handler (the key and value), and the regions
/// live (for a mark, 0).
const CONTROL_FRAME: u64 = 48;

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
    /// `adr` of the label into the register.
    Adr(Reg),
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
                Fix::Adr(t) => adr(t, d),
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
    /// Where a thunk a mark in tail position called returns: its mark's
    /// frame popped, and back to that frame's return address.
    mark_ret: Offset,
    /// The common trap, which every code's trap stubs go to.
    trap_stub: Offset,
    /// The common call of what is not native code, which every code's
    /// calls of it go to.
    foreign: Offset,
    /// The common making of a closure by call-out, which every code's
    /// closures go to when the inline path has no room.
    closure: Offset,
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
        let pop_mark = [ldp_post(FRAME, LINK, SP, CONTROL_FRAME as i64), ret()];
        let mark_ret = space.alloc(4 * pop_mark.len(), 16).ok_or("no room for the mark's return")?;
        space.write_code(mark_ret, &pop_mark);
        space.flush(mark_ret, 4 * pop_mark.len());
        let code = common_trap();
        let trap_stub = space.alloc(4 * code.len(), 16).ok_or("no room for the common trap")?;
        space.write_code(trap_stub, &code);
        space.flush(trap_stub, 4 * code.len());
        // Call-out 0: what is not native code, called (`common_foreign`);
        // 1: a closure made (`common_closure`).
        let callouts = vec![Callout::Foreign, Callout::ClosureAny];
        let code = common_foreign(0);
        let foreign = space.alloc(4 * code.len(), 16).ok_or("no room for the common foreign call")?;
        space.write_code(foreign, &code);
        space.flush(foreign, 4 * code.len());
        let code = common_closure(1);
        let closure = space.alloc(4 * code.len(), 16).ok_or("no room for the common closure")?;
        space.write_code(closure, &code);
        space.flush(closure, 4 * code.len());
        Ok(DirectMachine { space, entry, mark_ret, trap_stub, foreign, closure, stack: vec![0; STACK_WORDS], callouts })
    }

    /// Compile `closure`'s procedure, and every procedure it calls or
    /// makes closures of, to code in the native convention, each in a code
    /// bloblet of its own: what it compiled, the first first; or why it
    /// could not.
    pub fn compile(&mut self, heap: &mut Heap, closure: Value) -> Result<Vec<(String, Compiled)>, String> {
        let mut c = Compiling { heap: &*heap, procs: Vec::new(), by_word: HashMap::new(), queue: Vec::new(), callouts: &mut self.callouts, resume: None };
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
        let top = (self.stack.as_mut_ptr() as u64 + 8 * STACK_WORDS as u64) & !15;
        run(&self.runner(), rt, p, args, fuel, top)
    }

    fn runner(&self) -> Runner {
        Runner {
            entry: self.space.exec_addr(self.entry) as u64,
            mark_ret: self.space.exec_addr(self.mark_ret) as u64,
            trap_stub: self.space.exec_addr(self.trap_stub) as u64,
            foreign: self.space.exec_addr(self.foreign) as u64,
            closure: self.space.exec_addr(self.closure) as u64,
            table: self.callouts.as_ptr() as u64,
            stack_lo: self.stack.as_ptr() as u64,
        }
    }

    /// `p`'s instructions, as they are in its code bloblet.
    pub fn instructions(&self, heap: &Heap, p: Compiled) -> Vec<u32> {
        let bytes = heap.bloblet_bytes(p.code);
        (0..p.len).map(|i| u32::from_le_bytes(bytes[4 * i..4 * i + 4].try_into().expect("four bytes"))).collect()
    }
}

/// Run `p` with `args`, in at most about `fuel` steps, in `rt`, whose heap
/// its call-outs allocate in, on `r`'s machine's stack from `top` down.
fn run(r: &Runner, rt: &mut fixpt_runtime::Runtime, p: Compiled, args: &[Value], fuel: u64, top: u64) -> Result<Value, DirectTrap> {
    assert!(p.arity == usize::MAX || args.len() == p.arity, "the procedure's arity");
    assert!(args.len() <= 8, "arguments in registers only");
    THROWN.with(|t| t.set(None));
    let mut st = DState {
        stack_top: top,
        stack_limit: r.stack_lo + STACK_SLACK,
        fuel,
        callout: callout as *const () as u64,
        rt: rt as *mut fixpt_runtime::Runtime as u64,
        table: r.table,
        top: rt.heap.top_address() as u64,
        words: rt.heap.words_address() as u64,
        alloc_limit: rt.heap.inline_limit() as u64,
        regions: Value::fixnum(rt.heap.live_regions() as i64).raw(),
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
    (st.mark_ret, st.trap_stub, st.foreign, st.closure) = (r.mark_ret, r.trap_stub, r.foreign, r.closure);
    // SAFETY: the trampoline follows the C convention, saves what it
    // must, runs on the machine's stack from `top` (which outlives the
    // call, and which nothing else uses below `top` while it runs),
    // and touches only the state and that stack; the procedure's code,
    // compiled above, reads only its arguments and what they point to,
    // in the heap of `rt`, which is exclusively this call's while it
    // runs; it changes only in call-outs, which see every value the
    // native frames hold (`callout`).
    let entry: extern "C" fn(u64, u64, u64, u64) -> u64 = unsafe { std::mem::transmute(r.entry as usize) };
    let outer = RUNNING.replace(Some(*r));
    let v = entry(&mut st as *mut DState as u64, target, 0, 0);
    RUNNING.set(outer);
    if st.trap != 0 {
        let what = match LAST_MESSAGE.with(|m| m.borrow_mut().take()) {
            Some(m) if st.trap == PRIM_FAILED as u64 => m,
            _ => TRAPS[st.trap as usize].to_string(),
        };
        return Err(DirectTrap { what, pc: st.pc });
    }
    Ok(Value(v))
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

/// The common trap: the trap's kind (in X9) recorded, and where (the
/// return address, one past its site's stub), and the fuel; then back to
/// Rust. One for the machine: each code's stub for a kind is three
/// instructions that come here.
fn common_trap() -> Vec<u32> {
    let mut a = Asm::new();
    a.e(str(X9, ST, st_off(offset_of!(DState, trap))));
    a.e(sub_imm(X9, LINK, 4));
    a.e(str(X9, ST, st_off(offset_of!(DState, pc))));
    a.e(str(FUEL, ST, st_off(offset_of!(DState, fuel))));
    leave(&mut a);
    a.finish().expect("no labels")
}

/// The common call of what is not native code: from a code's stub for
/// such a call, with the arguments' count in X9 and the callee in CLO (a
/// `bl` or, in tail position, a `b`, so the return address is where to go
/// back to): a frame, the arguments into the state, call-out `n` (a
/// `Callout::Foreign`), and back with its value; or, if it failed, the
/// trap. One for the machine.
fn common_foreign(n: usize) -> Vec<u32> {
    let mut a = Asm::new();
    a.e(stp_pre(FRAME, LINK, SP, -16));
    a.e(add_imm(FRAME, SP, 0));
    a.e(str(X9, ST, st_off(offset_of!(DState, nargs))));
    a.e(str(CLO, ST, st_off(offset_of!(DState, aux))));
    let args = offset_of!(DState, args) as u32;
    for j in 0..8u32 {
        a.e(str(1 + j as Reg, ST, args + 8 * j));
    }
    call_out(&mut a, n);
    a.e(ldr(X9, ST, st_off(offset_of!(DState, trap))));
    a.e(cmp_imm(X9, 0));
    let (failed, stub) = (a.label(), a.label());
    a.to(failed, Fix::If(Cond::Ne));
    a.e(ldp_post(FRAME, LINK, SP, 16));
    a.e(ret());
    a.bind(failed);
    a.to(stub, Fix::Bl);
    a.bind(stub);
    a.e(movz(X9, PRIM_FAILED, 0));
    a.e(ldr(X16, ST, st_off(offset_of!(DState, trap_stub))));
    a.e(br(X16));
    a.finish().expect("labels bound")
}

/// The common making of a closure by call-out: from a code's closure site
/// whose inline path had no room, with the count of free values (in
/// REG1…REGn) in X9 and the code in X17, by `blr`: a frame, what it needs
/// into the state, call-out `n` (a `Callout::ClosureAny`), and back with
/// the closure; or, if it failed, the trap. One for the machine.
fn common_closure(n: usize) -> Vec<u32> {
    let mut a = Asm::new();
    a.e(stp_pre(FRAME, LINK, SP, -16));
    a.e(add_imm(FRAME, SP, 0));
    a.e(str(X9, ST, st_off(offset_of!(DState, nargs))));
    a.e(str(X17, ST, st_off(offset_of!(DState, aux))));
    let args = offset_of!(DState, args) as u32;
    for j in 0..8u32 {
        a.e(str(1 + j as Reg, ST, args + 8 * j));
    }
    call_out(&mut a, n);
    a.e(ldr(X9, ST, st_off(offset_of!(DState, trap))));
    a.e(cmp_imm(X9, 0));
    let (failed, stub) = (a.label(), a.label());
    a.to(failed, Fix::If(Cond::Ne));
    a.e(ldp_post(FRAME, LINK, SP, 16));
    a.e(ret());
    a.bind(failed);
    a.to(stub, Fix::Bl);
    a.bind(stub);
    a.e(movz(X9, PRIM_FAILED, 0));
    a.e(ldr(X16, ST, st_off(offset_of!(DState, trap_stub))));
    a.e(br(X16));
    a.finish().expect("labels bound")
}

/// Where a call-out that does not return to its caller said to go: its
/// stack, frame and value, and there.
fn resume(a: &mut Asm) {
    a.e(ldr(X9, ST, st_off(offset_of!(DState, resume_sp))));
    a.e(add_imm(SP, X9, 0));
    a.e(ldr(FRAME, ST, st_off(offset_of!(DState, resume_fp))));
    a.e(ldr(RESULT, ST, st_off(offset_of!(DState, resume_x0))));
    a.e(ldr(X16, ST, st_off(offset_of!(DState, resume_pc))));
    a.e(br(X16));
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
    /// The continuation procedure, once a procedure takes a continuation.
    resume: Option<usize>,
}

impl Compiling<'_> {
    /// The continuation procedure: what a continuation's native closure
    /// runs, given the value (in `x1`), the closure in `CLO`. In a frame of
    /// its own, it calls out to put the continuation's frames back, which
    /// it replaces (`Callout::Reinstate`), and goes where they resume.
    fn resume_proc(&mut self) -> usize {
        if let Some(q) = self.resume {
            return q;
        }
        let mut a = Asm::new();
        a.e(stp_pre(FRAME, LINK, SP, -16));
        a.e(add_imm(FRAME, SP, 0));
        let args = offset_of!(DState, args) as u32;
        a.e(str(1, ST, args));
        a.e(str(CLO, ST, args + 8));
        let n = self.callouts.len();
        self.callouts.push(Callout::Reinstate);
        call_out(&mut a, n);
        let failed = a.label();
        a.e(ldr(X9, ST, st_off(offset_of!(DState, trap))));
        a.e(cmp_imm(X9, 0));
        a.to(failed, Fix::If(Cond::Ne));
        resume(&mut a);
        a.bind(failed);
        a.e(str(FUEL, ST, st_off(offset_of!(DState, fuel))));
        leave(&mut a);
        let code = a.finish().expect("placed");
        let q = self.procs.len();
        self.procs.push(Proc { word: Value::FALSE, rw: Value::FALSE, name: "continuation".into(), arity: 1, fields: vec![Field::Myself, Field::Const(Value::FALSE)], len: code.len(), code });
        self.resume = Some(q);
        q
    }

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
        self.procs.push(Proc { word, rw, name: self.name(word), arity, fields: vec![Field::Myself, Field::Const(word)], code: Vec::new(), len: 0 });
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
        // A cellular closure of no register code (an adapter) cannot be
        // compiled: called through its cell, as what is not native code.
        if let Some((word, free)) = self.closure_parts(v)
            && self.name(word) != "undefined"
            && self.heap.is_register_word(self.heap.bloblet_slot(word, WORD_TWIN))
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
                "branch" | "branchf" | "brancht" | "global-guard" => {
                    let to = i as i64 + 1 + n as i64 + cells[i + n].as_fixnum();
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
        // Whether this procedure's frame is pushed where each instruction
        // starts: a body's fast version may be a leaf, with no frame, where
        // its plain one has one (`regcode::register_code`). After `save`,
        // pushed; after `pop`, not; where a branch goes, as at the branch.
        let mut framed = vec![false; cells.len() + 1];
        {
            let mut known: Vec<Option<bool>> = vec![None; cells.len() + 1];
            let mut cur = false;
            for &i in &starts {
                if let Some(k) = known[i] {
                    cur = k;
                }
                framed[i] = cur;
                let (op, n, _) = OPS[cells[i].as_fixnum() as usize];
                match op {
                    "save" => cur = true,
                    "pop" => cur = false,
                    "branch" | "branchf" | "brancht" | "global-guard" => {
                        let to = (i as i64 + 1 + n as i64 + cells[i + n].as_fixnum()) as usize;
                        known[to].get_or_insert(cur);
                    }
                    _ => {}
                }
            }
        }
        // What each `global` is for: a call just after it (a tail call's
        // frame popped between), or its value.
        let called = |j: usize| {
            let at = starts.iter().position(|&s| s == j).expect("an instruction");
            starts[at + 1..].iter().copied().find(|&c| op_at(c) != "pop").filter(|&c| matches!(op_at(c), "invoke" | "tailinvoke"))
        };
        // The frame: the link and return address, its stack map (a header,
        // the mask of the slots traced), register code's slots, then this
        // code bloblet and the closure running.
        if frame.is_some_and(|m| 24 + 8 * (m + 2) > 504) {
            return decline("a frame too large for one `stp`".into());
        }
        let size = frame.map(|m| (24 + 8 * (m as u32 + 2)).div_ceil(16) * 16);
        let self_slot = frame.map(|m| 24 + 8 * m as u32);
        let clo_slot = frame.map(|m| 24 + 8 * (m as u32 + 1));
        // Which slots are live after each instruction: a backward pass over
        // register code's slots (`stack` and `load` read one, `setstk` and
        // `store` write one), for the stack map a frame stores before each
        // call and call-out (`docs/research/generational-gc.md`).
        let live_out = {
            let at_of: HashMap<usize, usize> = starts.iter().enumerate().map(|(si, &i)| (i, si)).collect();
            let ns = starts.len();
            let (mut uses, mut defs) = (vec![0u64; ns], vec![0u64; ns]);
            let mut succ: Vec<Vec<usize>> = vec![Vec::new(); ns];
            for (si, &i) in starts.iter().enumerate() {
                let (op, n, _) = OPS[cells[i].as_fixnum() as usize];
                let bit = |j: usize| 1u64 << cells[i + 1 + j].as_fixnum();
                match op {
                    "stack" => uses[si] |= bit(0),
                    "load" => uses[si] |= bit(1),
                    "setstk" => defs[si] |= bit(0),
                    "store" => defs[si] |= bit(1),
                    _ => {}
                }
                let to = || at_of[&((i as i64 + 1 + n as i64 + cells[i + n].as_fixnum()) as usize)];
                match op {
                    "return" | "tailinvoke" => {}
                    "branch" => succ[si].push(to()),
                    "branchf" | "brancht" | "global-guard" => succ[si].extend([si + 1, to()]),
                    _ if si + 1 < ns => succ[si].push(si + 1),
                    _ => {}
                }
            }
            let (mut live_in, mut live_out) = (vec![0u64; ns], vec![0u64; ns]);
            loop {
                let mut changed = false;
                for si in (0..ns).rev() {
                    let out = succ[si].iter().fold(0, |m, &t| m | live_in[t]);
                    let inn = (out & !defs[si]) | uses[si];
                    if (out, inn) != (live_out[si], live_in[si]) {
                        (live_out[si], live_in[si], changed) = (out, inn, true);
                    }
                }
                if !changed {
                    break live_out;
                }
            }
        };
        // The stack map stored where a collection may come, unless the same
        // one is stored already on the only way here.
        let mut map_stored: Option<u64> = None;
        let mut a = Asm::new();
        let entry = a.label();
        let labels: Vec<Label> = (0..=cells.len()).map(|_| a.label()).collect();
        // Each trap site branches to a stub of its own, which calls the
        // trap's code: so the return address says where it was.
        let mut stubs: Vec<(Label, u32)> = Vec::new();
        // Each call of what may not be native code branches, when it is
        // not, to a stub of its own (with where to come back to, how many
        // arguments, and whether a tail call), which calls the common
        // routine that calls out for it.
        let mut foreign: Vec<(Label, Label, usize, bool)> = Vec::new();
        // Where a call-out that does not return goes on (an abort), if one
        // does here.
        let (resume_at, mut uses_resume) = (a.label(), false);
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
            if target[i] {
                map_stored = None;
            }
            // Before what may collect, in a frame: the slots live after it,
            // the code bloblet's, and the closure's if the code reads it.
            if let Some(m) = frame
                && framed[i]
                && (matches!(op, "prim" | "cellular" | "lambda" | "invokeself") || op == "invoke")
            {
                let map = live_out[si - 1] | 1 << m | if captures { 1 << (m + 1) } else { 0 };
                if map_stored != Some(map) {
                    a.es(&mov_imm64(X16, Value::fixnum(map as i64).raw()));
                    a.e(str(X16, FRAME, 16));
                    map_stored = Some(map);
                }
            }
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
                    } else if let Some((word, free)) = self.closure_parts(v)
                        && free.is_empty()
                        && self.name(word) != "undefined"
                    {
                        // A closure over nothing that the compiler made (a
                        // lambda-lifted procedure's): its code, compiled,
                        // called straight, as a global's is; as a value, a
                        // native closure of it.
                        let q = self.proc_of(word).map_err(|e| format!("`{name}` calls {e}"))?;
                        if called(i).is_some() {
                            pending = Some(Field::Code(q));
                        } else {
                            let f = self.field(p, Field::Closure(q, vec![]));
                            ldr_field(&mut a, RESULT, f);
                        }
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
                // Decided here where the cell holds a cellular closure, as
                // that global's value is when this code is made
                // (`global_value`): nothing, where it is a closure of the
                // word; else the test, which the code runs: the value's field
                // 2, a cellular closure's word or a native closure's code,
                // whose field 2 is the word it was compiled from.
                "global-guard" => {
                    let (cell, w, to) = (o(0), o(1), (i as i64 + 4 + o(2).as_fixnum()) as usize);
                    if !self.closure_parts(self.heap.bloblet_slot(cell, 2)).is_some_and(|(word, _)| word == w) {
                        let held = a.label();
                        let fc = self.field(p, Field::Cell(cell));
                        ldr_field(&mut a, X9, fc);
                        a.e(ldur(X11, X9, field_off(2)));
                        a.e(ldur(X11, X11, field_off(CLOSURE_WORD)));
                        let fw = self.field(p, Field::Const(w));
                        ldr_field(&mut a, X16, fw);
                        a.e(cmp(X11, X16));
                        a.to(held, Fix::If(Cond::Eq));
                        a.e(ldur(X11, X11, field_off(fixpt_heap::layout::cellular::CODE_SOURCE)));
                        a.e(cmp(X11, X16));
                        a.to(labels[to], Fix::If(Cond::Ne));
                        a.bind(held);
                    }
                }
                "setglbl" => {
                    let f = self.field(p, Field::Cell(o(0)));
                    ldr_field(&mut a, X9, f);
                    a.e(stur(RESULT, X9, field_off(2)));
                }
                "lexical" => {
                    let from = match clo_slot.filter(|_| framed[i]) {
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
                // for any one frame below it); this code bloblet in its slot,
                // so that the frame keeps it alive; the closure in its, if
                // the code reads it. Its slots are not cleared: a
                // collection traces only those its stack map says are live,
                // each written before. One read before any write on some
                // way (no register compiler makes one) is cleared.
                "save" => {
                    let size = size.expect("a frame") as i64;
                    a.e(stp_pre(FRAME, LINK, SP, -size));
                    a.e(add_imm(FRAME, SP, 0));
                    a.e(cmp_sp(LIMIT));
                    trap(&mut a, &mut stubs, STACK_OVERFLOW, Cond::Lo);
                    map_stored = None;
                    let unwritten = live_out[si - 1];
                    for k in (0..64).filter(|k| unwritten & (1 << k) != 0) {
                        a.e(str(XZR, FRAME, 24 + 8 * k));
                    }
                    ldr_field(&mut a, X9, 1);
                    a.e(str(X9, FRAME, self_slot.expect("a frame")));
                    if captures {
                        a.e(str(CLO, FRAME, clo_slot.expect("a frame")));
                    }
                }
                "pop" => a.e(ldp_post(FRAME, LINK, SP, size.expect("a frame") as i64)),
                "stack" => a.e(ldr(RESULT, FRAME, 24 + 8 * k(o(0)) as u32)),
                "setstk" => a.e(str(RESULT, FRAME, 24 + 8 * k(o(0)) as u32)),
                "load" => a.e(ldr(reg(o(0)), FRAME, 24 + 8 * k(o(1)) as u32)),
                "store" => {
                    a.e(str(reg(o(0)), FRAME, 24 + 8 * k(o(1)) as u32));
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
                                if matches!(op_at(j), "branchf" | "brancht")
                                    && starts.get(si + 1).is_none_or(|&f| sets_first(f))
                                    && sets_first((j as i64 + 2 + cells[j + 1].as_fixnum()) as usize) =>
                            {
                                a.bind(labels[j]);
                                let to = (j as i64 + 2 + cells[j + 1].as_fixnum()) as usize;
                                // `branchf` goes where the test fails; `brancht`
                                // where it holds.
                                let cond = match (op_at(j), r) {
                                    ("branchf", "eq") => Cond::Ne,
                                    ("branchf", _) => Cond::Ge,
                                    (_, "eq") => Cond::Eq,
                                    _ => Cond::Lt,
                                };
                                a.to(labels[to], Fix::If(cond));
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
                // Control, on the native stack (`docs/research/
                // native-conventions.md`, step 5). A prompt, and a mark, is a
                // frame of its own around the thunk's call, which the frames'
                // walk finds; the rest are call-outs, which walk the frames,
                // and take and put back runs of them.
                "cellular" if matches!(ROUTINES.get(k(o(0))).map(|r| r.0), Some("prompt" | "withmark" | "withmark-tail" | "abort" | "callcc" | "callcomp" | "firstmark" | "currentmarks" | "marksof")) => {
                    if frame.is_none() {
                        return decline("a call-out outside a frame".into());
                    }
                    let args = offset_of!(DState, args) as u32;
                    // A call of the closure in `CLO`, `n` arguments in
                    // registers, back at `after`: native code, or not.
                    let call_clo = |a: &mut Asm, foreign: &mut Vec<(Label, Label, usize, bool)>, n: usize, after: Label| {
                        let stub = a.label();
                        a.e(ldur(X16, CLO, field_off(CLOSURE_WORD)));
                        a.e(ldr(X17, ST, st_off(offset_of!(DState, code_lo))));
                        a.e(cmp(X16, X17));
                        a.to(stub, Fix::If(Cond::Lo));
                        foreign.push((stub, after, n, false));
                        a.e(add(X16, X16, DELTA));
                        a.e(blr(X16));
                        a.bind(after);
                    };
                    let callout = |a: &mut Asm, stubs: &mut Vec<(Label, u32)>, callouts: &mut Vec<Callout>, c: Callout| {
                        let n = callouts.len();
                        callouts.push(c);
                        for j in 0..c.arity() {
                            a.e(str(1 + j as Reg, ST, args + 8 * j as u32));
                        }
                        call_out(a, n);
                        a.e(ldr(X9, ST, st_off(offset_of!(DState, trap))));
                        a.e(cmp_imm(X9, 0));
                        trap(a, stubs, PRIM_FAILED, Cond::Ne);
                    };
                    // A control frame: the link, `second` (the landing, or
                    // nothing), the marker, `x1` and `x2`, and `last`.
                    let control_frame = |a: &mut Asm, stubs: &mut Vec<(Label, u32)>, second: Reg, marker: Value, last: Option<u32>| {
                        a.e(stp_pre(FRAME, second, SP, -(CONTROL_FRAME as i64)));
                        a.e(add_imm(FRAME, SP, 0));
                        a.e(cmp_sp(LIMIT));
                        trap(a, stubs, STACK_OVERFLOW, Cond::Lo);
                        a.es(&mov_imm64(X16, marker.raw()));
                        a.e(str(X16, FRAME, 16));
                        a.e(str(1, FRAME, 24));
                        a.e(str(2, FRAME, 32));
                        match last {
                            Some(off) => {
                                a.e(ldr(X16, ST, off));
                                a.e(str(X16, FRAME, 40));
                            }
                            None => a.e(str(XZR, FRAME, 40)),
                        }
                    };
                    let pop_control = |a: &mut Asm| {
                        a.e(ldr(FRAME, SP, 0));
                        a.e(add_imm(SP, SP, CONTROL_FRAME as u32));
                    };
                    match ROUTINES[k(o(0))].0 {
                        // `x1` the tag, `x2` the handler, `x3` the thunk. An
                        // abort resumes at the landing, the prompt's frame on
                        // top, with the value: the handler called with it.
                        "prompt" => {
                            let (land, after, done, handled) = (a.label(), a.label(), a.label(), a.label());
                            a.to(land, Fix::Adr(X9));
                            control_frame(&mut a, &mut stubs, X9, PROMPT_MARK, Some(st_off(offset_of!(DState, regions))));
                            a.e(mov(CLO, 3));
                            call_clo(&mut a, &mut foreign, 0, after);
                            pop_control(&mut a);
                            a.to(done, Fix::B);
                            a.bind(land);
                            a.e(mov(1, RESULT));
                            a.e(ldr(CLO, SP, 32));
                            pop_control(&mut a);
                            call_clo(&mut a, &mut foreign, 1, handled);
                            a.bind(done);
                        }
                        // `x1` the key, `x2` the value, `x3` the thunk.
                        "withmark" => {
                            let after = a.label();
                            control_frame(&mut a, &mut stubs, XZR, MARK_MARK, None);
                            a.e(mov(CLO, 3));
                            call_clo(&mut a, &mut foreign, 0, after);
                            pop_control(&mut a);
                        }
                        // In tail position, this frame popped: `x1` the key,
                        // `x2` the value, `x3` the thunk, tail-called with the
                        // mark's frame under it, returning through
                        // `mark_ret`, which pops that frame. Returning there
                        // already, a mark's frame is on top: one for the same
                        // key has its value replaced, as the cellular
                        // machine's `withmark-tail` does, so that a loop that
                        // marks each time runs in constant space.
                        "withmark-tail" => {
                            let (push, call, stub, after) = (a.label(), a.label(), a.label(), a.label());
                            a.e(ldr(X9, ST, st_off(offset_of!(DState, mark_ret))));
                            a.e(cmp(LINK, X9));
                            a.to(push, Fix::If(Cond::Ne));
                            a.e(ldr(X16, SP, 24));
                            a.e(cmp(X16, 1));
                            a.to(push, Fix::If(Cond::Ne));
                            a.e(str(2, SP, 32));
                            a.to(call, Fix::B);
                            a.bind(push);
                            control_frame(&mut a, &mut stubs, LINK, MARK_MARK, None);
                            a.e(ldr(LINK, ST, st_off(offset_of!(DState, mark_ret))));
                            a.bind(call);
                            a.e(mov(CLO, 3));
                            a.e(ldur(X16, CLO, field_off(CLOSURE_WORD)));
                            a.e(ldr(X17, ST, st_off(offset_of!(DState, code_lo))));
                            a.e(cmp(X16, X17));
                            a.to(stub, Fix::If(Cond::Lo));
                            foreign.push((stub, after, 0, true));
                            a.e(add(X16, X16, DELTA));
                            a.e(br(X16));
                            a.bind(after);
                        }
                        "abort" => {
                            callout(&mut a, &mut stubs, self.callouts, Callout::Abort);
                            uses_resume = true;
                            a.to(resume_at, Fix::B);
                        }
                        // The continuation resumes where `f`'s call returns:
                        // it is taken, and `f` called with it.
                        r @ ("callcc" | "callcomp") => {
                            let after = a.label();
                            a.to(after, Fix::Adr(X9));
                            a.e(str(X9, ST, st_off(offset_of!(DState, ret_pc))));
                            let q = self.resume_proc();
                            let f = self.field(p, Field::Code(q));
                            ldr_field(&mut a, X9, f);
                            a.e(str(X9, ST, st_off(offset_of!(DState, aux))));
                            callout(&mut a, &mut stubs, self.callouts, Callout::Capture { whole: r == "callcc" });
                            a.e(mov(1, RESULT));
                            a.e(ldr(CLO, ST, args));
                            call_clo(&mut a, &mut foreign, 1, after);
                        }
                        "firstmark" => callout(&mut a, &mut stubs, self.callouts, Callout::FirstMark),
                        "currentmarks" => callout(&mut a, &mut stubs, self.callouts, Callout::CurrentMarks),
                        _ => callout(&mut a, &mut stubs, self.callouts, Callout::MarksOf),
                    }
                }
                // A call-out: to Rust, on Rust's stack, which may collect;
                // everything live is in the frame by then (register code
                // sees to it), and the arguments go through the state.
                "prim" | "cellular" | "lambda" => {
                    // A closure's code: this bloblet's field.
                    let mut code_field = None;
                    let c = match (op, ROUTINES.get(k(o(0))).map(|r| r.0)) {
                        ("lambda", _) => {
                            let q = self.proc_of(o(0)).map_err(|e| format!("`{name}` makes a closure of {e}"))?;
                            code_field = Some(self.field(p, Field::Code(q)));
                            Callout::Closure { n: k(o(1)) }
                        }
                        ("cellular", Some("cons")) if k(o(1)) == 2 => Callout::Cons,
                        ("cellular", Some("field@")) if k(o(1)) == 2 => Callout::FieldRef,
                        ("prim", _) => match fixpt_runtime::PRIMITIVES.get(k(o(0))) {
                            Some(d) if d.name == "%region-closure" => Callout::RegionClosure { n: k(o(1)) },
                            // By design: a procedure calling `stay-cellular`
                            // runs as cellular code.
                            Some(d) if d.name == "%stay-cellular" => return decline("it calls `stay-cellular`".into()),
                            Some(d) if matches!(d.kind, fixpt_runtime::PrimKind::Simple(_)) && d.accepts(k(o(1))) => {
                                Callout::Prim { p: k(o(0)), n: k(o(1)) }
                            }
                            Some(d) => return decline(format!("the primitive `{}`", d.name)),
                            None => return decline(format!("primitive {}", k(o(0)))),
                        },
                        (_, r) => return decline(format!("the routine `{}`", r.unwrap_or("?"))),
                    };
                    // A leaf may make a closure (register code makes it one only
                    // where the closure is its value): its slow path makes a
                    // frame of its own around the call-out.
                    let leaf_closure = frame.is_none() && matches!(c, Callout::Closure { .. });
                    if frame.is_none() && !leaf_closure {
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
                    // Field `x2` (8k, a fixnum) of the bloblet in `x1`, whose
                    // trailer says how many it has: 2 ≤ k ≤ F, else the
                    // call-out reports it.
                    if let Callout::FieldRef = c {
                        let tag = fixpt_heap::value::TAG_TRAILER as u32;
                        a.e(ldur(X16, 1, field_off(1)));
                        a.e(and_low(X13, X16, 3));
                        a.e(cmp_imm(X13, tag));
                        a.to(slow, Fix::If(Cond::Ne));
                        a.e(cmp_imm(2, 16));
                        a.to(slow, Fix::If(Cond::Lt));
                        a.e(sub_imm(X16, X16, tag));
                        a.e(cmp(2, X16));
                        a.to(slow, Fix::If(Cond::Gt));
                        a.e(sub(X11, 1, 2));
                        a.e(ldur(RESULT, X11, -4));
                        a.to(done, Fix::B);
                    }
                    // A native closure over REG1…REGn likewise, from the free
                    // space: its header; its free values, the code, and the
                    // trailer, fields counted back from where it points.
                    if let (Callout::Closure { n }, Some(f)) = (c, code_field) {
                        let total = n + 2;
                        a.e(ldr(X13, ST, st_off(offset_of!(DState, top))));
                        a.e(ldr(X14, X13, 0));
                        a.e(ldr(X15, ST, st_off(offset_of!(DState, alloc_limit))));
                        a.e(add_imm(X16, X14, (total + 1) as u32));
                        a.e(cmp(X16, X15));
                        a.to(slow, Fix::If(Cond::Hi));
                        a.e(ldr(X9, ST, st_off(offset_of!(DState, words))));
                        a.e(add_lsl(X11, X9, X14, 3));
                        let header = fixpt_heap::value::make_header(fixpt_heap::layout::kind("native-closure"), total, 0);
                        a.es(&mov_imm64(X17, header));
                        a.e(str(X17, X11, 0));
                        for i in 0..n {
                            a.e(str(1 + i as Reg, X11, 8 * (n - i) as u32));
                        }
                        ldr_field(&mut a, X17, f);
                        a.e(str(X17, X11, 8 * (n + 1) as u32));
                        let trailer = fixpt_heap::layout::T_DISTANCE.put(fixpt_heap::value::TAG_TRAILER, total as u64);
                        a.es(&mov_imm64(X17, trailer));
                        a.e(str(X17, X11, 8 * total as u32));
                        a.e(str(X16, X13, 0));
                        a.e(add_imm(RESULT, X11, (8 * (total + 1)) as u32 + fixpt_heap::value::TAG_BLOBLET as u32));
                        a.to(done, Fix::B);
                    }
                    a.bind(slow);
                    // A closure the free space had no room for: the
                    // machine's common routine makes it.
                    if let (Callout::Closure { n }, Some(f)) = (c, code_field) {
                        if leaf_closure {
                            // The return address kept, and a frame for the
                            // collector to walk, with nothing in it.
                            a.e(stp_pre(FRAME, LINK, SP, -16));
                            a.e(add_imm(FRAME, SP, 0));
                        }
                        ldr_field(&mut a, X17, f);
                        a.e(movz(X9, n as u32, 0));
                        a.e(ldr(X16, ST, st_off(offset_of!(DState, closure))));
                        a.e(blr(X16));
                        if leaf_closure {
                            a.e(ldp_post(FRAME, LINK, SP, 16));
                        }
                    } else {
                        let n = self.callouts.len();
                        self.callouts.push(c);
                        let args = offset_of!(DState, args) as u32;
                        for j in 0..c.arity() {
                            a.e(str(1 + j as Reg, ST, args + 8 * j as u32));
                        }
                        call_out(&mut a, n);
                        a.e(ldr(X9, ST, st_off(offset_of!(DState, trap))));
                        a.e(cmp_imm(X9, 0));
                        trap(&mut a, &mut stubs, PRIM_FAILED, Cond::Ne);
                    }
                    a.bind(done);
                }
                // A call. Of a global's procedure that captures nothing: its
                // code, from this bloblet's field, entered at its start. Of
                // any other procedure: a native closure, in `CLO`, whose
                // field 2 is its code, entered so; one whose field 2 is not
                // in the code area is not native code, and traps.
                "invoke" | "tailinvoke" => {
                    let tail = op == "tailinvoke";
                    let (stub, after) = (a.label(), a.label());
                    let not_native = |a: &mut Asm| {
                        a.e(ldur(X16, CLO, field_off(CLOSURE_WORD)));
                        a.e(ldr(X17, ST, st_off(offset_of!(DState, code_lo))));
                        a.e(cmp(X16, X17));
                        a.to(stub, Fix::If(Cond::Lo));
                    };
                    match pending.take() {
                        Some(Field::Code(q)) => {
                            let f = self.field(p, Field::Code(q));
                            ldr_field(&mut a, X16, f);
                        }
                        // Through the global's cell, when the code runs: what
                        // it holds then, native code or not.
                        Some(Field::Cell(c)) => {
                            let f = self.field(p, Field::Cell(c));
                            ldr_field(&mut a, X9, f);
                            a.e(ldur(CLO, X9, field_off(2)));
                            not_native(&mut a);
                            foreign.push((stub, after, k(o(0)), tail));
                        }
                        Some(g) => {
                            let f = self.field(p, g);
                            ldr_field(&mut a, CLO, f);
                            a.e(ldur(X16, CLO, field_off(CLOSURE_WORD)));
                        }
                        None => {
                            a.e(mov(CLO, RESULT));
                            not_native(&mut a);
                            foreign.push((stub, after, k(o(0)), tail));
                        }
                    }
                    a.e(add(X16, X16, DELTA));
                    a.e(if tail { br(X16) } else { blr(X16) });
                    a.bind(after);
                }
                "invokeself" => {
                    if let Some(s) = clo_slot.filter(|_| captures) {
                        a.e(ldr(CLO, FRAME, s));
                    }
                    a.to(entry, Fix::Bl);
                }
                "return" => a.e(ret()),
                "branch" | "branchf" | "brancht" => {
                    let to = (i as i64 + 2 + o(0).as_fixnum()) as usize;
                    if op != "branch" {
                        a.es(&mov_imm64(X16, Value::FALSE.raw()));
                        a.e(cmp(RESULT, X16));
                        a.to(labels[to], Fix::If(if op == "branchf" { Cond::Eq } else { Cond::Ne }));
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
        let own = a.code.len();
        // The calls of what is not native code, out of the way: the common
        // routine, in a frame of its own with nothing in it, calls out with
        // the arguments and the callee, and returns its value; a tail call
        // goes there to return from it to this procedure's caller.
        // Each call of what is not native code: to the machine's common
        // routine (`common_foreign`), with the arguments' count.
        for (stub, after, n, tail) in &foreign {
            a.bind(*stub);
            a.e(movz(X9, *n as u32, 0));
            a.e(ldr(X16, ST, st_off(offset_of!(DState, foreign))));
            if *tail {
                a.e(br(X16));
            } else {
                a.e(blr(X16));
                a.to(*after, Fix::B);
            }
        }
        if uses_resume {
            a.bind(resume_at);
            resume(&mut a);
        }
        // The traps, out of the way: a stub per site, calling its kind's
        // stub, which goes to the machine's common trap (`common_trap`),
        // which records the trap and where, and leaves.
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
            a.e(ldr(X16, ST, st_off(offset_of!(DState, trap_stub))));
            a.e(br(X16));
        }
        self.procs[p].code = a.finish()?;
        self.procs[p].len = own;
        Ok(())
    }
}

/// Call-out `n`, its arguments in the state already: on Rust's stack,
/// with where the native frames are for its collections to find.
fn call_out(a: &mut Asm, n: usize) {
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
    let n = if let Callout::Foreign | Callout::ClosureAny = c { st.nargs as usize } else { c.arity() };
    let mut args: Vec<Value> = st.args[..n].iter().map(|a| Value(*a)).collect();
    if let Callout::Foreign = c {
        args.push(Value(st.aux));
    }
    let mut code = [Value(st.code)];
    // The frames walked only for a collection.
    if rt.heap.collection_due() {
        let mut roots = native_frames(st);
        roots.push(&mut args);
        roots.push(&mut code);
        rt.heap.collect(&mut roots);
    }
    let out = match c {
        Callout::Cons => rt.heap.cons(args[0], args[1]).raw(),
        Callout::Closure { .. } | Callout::ClosureAny => native_closure(&mut rt.heap, Value(st.aux), &args).raw(),
        Callout::RegionClosure { n } => {
            let h = if args[0].is_fixnum() { args[0].as_fixnum() as usize } else { usize::MAX };
            let (free, code) = (&args[1..n - 1], args[n - 1]);
            rt.heap.in_region(h, |heap| native_closure(heap, code, free)).raw()
        }
        Callout::Foreign => {
            let (f, args) = args.split_last().expect("the callee");
            // What the native frames hold, kept where the heap roots it while
            // the cellular machine runs, which may collect; then put back.
            let held: Vec<Value> = native_frames(st).iter().flat_map(|s| s.iter().copied()).collect();
            let kept = rt.heap.vector_from(&held);
            let at = rt.heap.push_root(kept);
            // A native call from the cellular code runs below these frames.
            let runner = RUNNING.get().expect("native code is running");
            let outer = CALLED_OUT.replace(Some((runner, st.native_sp)));
            let r = fixpt_engine::cellular::call_value(rt, *f, args);
            CALLED_OUT.set(outer);
            let kept = rt.heap.root_at(at);
            rt.heap.pop_roots_to(at);
            let mut i = 0;
            for s in native_frames(st) {
                for v in s.iter_mut() {
                    *v = rt.heap.obj_ref(kept, i);
                    i += 1;
                }
            }
            match r {
                Ok(v) => v.raw(),
                Err(e) => {
                    match e {
                        fixpt_runtime::NativeExit::Failed(m) => LAST_MESSAGE.with(|c| *c.borrow_mut() = Some(m)),
                        fixpt_runtime::NativeExit::Throw { k, v } => {
                            THROWN.with(|t| t.set(Some((k, v))));
                            LAST_MESSAGE.with(|c| *c.borrow_mut() = Some("a continuation of cellular code was thrown past native code".into()));
                        }
                    }
                    st.trap = PRIM_FAILED as u64;
                    0
                }
            }
        }
        Callout::FieldRef => {
            let k = if args[1].is_fixnum() { usize::try_from(args[1].as_fixnum()).ok() } else { None };
            match k.and_then(|k| rt.heap.bloblet_field(args[0], k).ok()) {
                Some(v) => v.raw(),
                None => {
                    let m = format!("field@: no field {} of {}", fixpt_engine::cellular::describe(rt, args[1]), fixpt_engine::cellular::describe(rt, args[0]));
                    LAST_MESSAGE.with(|c| *c.borrow_mut() = Some(m));
                    st.trap = PRIM_FAILED as u64;
                    0
                }
            }
        }
        Callout::Abort => match frames_of(st).into_iter().find(|&(fp, end)| is_control(fp, end, PROMPT_MARK, args[0])) {
            // The prompt's frame on top, resumed at its landing, with what
            // the regions entered inside it held gone.
            Some((pf, _)) => {
                rt.heap.region_exit(Value(word(pf + 40)).as_fixnum() as usize);
                (st.resume_sp, st.resume_fp, st.resume_pc, st.resume_x0) = (pf, pf, word(pf + 8), args[1].raw());
                0
            }
            None => failed(st, "abort: no prompt for this tag".into()),
        },
        Callout::Capture { whole } => {
            // `f`, moved by a collection, where the code reads it.
            st.args[0] = args[0].raw();
            let frames = frames_of(st);
            let end = if whole {
                Some(st.stack_top)
            } else {
                frames.iter().find(|&&(fp, end)| is_control(fp, end, PROMPT_MARK, args[1])).map(|&(fp, _)| fp)
            };
            match end {
                Some(end) => capture(rt, st, &frames, end, whole).raw(),
                None => failed(st, "call-with-composable-continuation: no prompt for this tag".into()),
            }
        }
        Callout::Reinstate => reinstate(rt, st, args[1], args[0]),
        Callout::FirstMark => {
            let found = frames_of(st).into_iter().find(|&(fp, end)| is_control(fp, end, MARK_MARK, args[0]));
            found.map_or(args[1], |(fp, _)| Value(word(fp + 32))).raw()
        }
        Callout::CurrentMarks => {
            let marks: Vec<Value> =
                frames_of(st).into_iter().filter(|&(fp, end)| is_control(fp, end, MARK_MARK, args[0])).map(|(fp, _)| Value(word(fp + 32))).collect();
            rt.heap.list_from(&marks).raw()
        }
        Callout::MarksOf => match marks_of(&rt.heap, args[0], args[1]) {
            Some(marks) => rt.heap.list_from(&marks).raw(),
            None => failed(st, "marks-of: not a continuation".into()),
        },
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
    // Where the heap is now, and how far native code may allocate in it;
    // how many regions are live.
    st.words = rt.heap.words_address() as u64;
    st.alloc_limit = rt.heap.inline_limit() as u64;
    st.regions = Value::fixnum(rt.heap.live_regions() as i64).raw();
    out
}

/// A call-out's failure, saying why: the call traps.
fn failed(st: &mut DState, why: String) -> u64 {
    LAST_MESSAGE.with(|c| *c.borrow_mut() = Some(why));
    st.trap = PRIM_FAILED as u64;
    0
}

/// The word at `at`, on the native stack.
fn word(at: u64) -> u64 {
    // SAFETY: a word of a frame on the native stack, which the call-out's
    // caller made and which lives while it runs.
    unsafe { *(at as *const u64) }
}

fn set_word(at: u64, w: u64) {
    // SAFETY: a word of the native stack, above its limit, which no Rust
    // code holds while the call-out runs.
    unsafe { *(at as *mut u64) = w }
}

/// Each native frame, innermost first, from the one that called out: where
/// it starts, and where it ends (its caller's frame, or the stack's top).
fn frames_of(st: &DState) -> Vec<(u64, u64)> {
    let mut out = Vec::new();
    let mut fp = st.fp;
    while fp != 0 && fp < st.stack_top {
        let caller = word(fp);
        let end = if caller > fp && caller <= st.stack_top { caller } else { st.stack_top };
        out.push((fp, end));
        fp = if end == caller { caller } else { 0 };
    }
    out
}

/// Whether the frame at `fp` is a control frame of `marker` for `key`.
fn is_control(fp: u64, end: u64, marker: Value, key: Value) -> bool {
    end - fp == CONTROL_FRAME && word(fp + 16) == marker.raw() && word(fp + 24) == key.raw()
}

/// The continuation of the frames from the one that called out up to `end`
/// (the stack's top, or a prompt's frame), resumed where the state's
/// `ret_pc` says: a native closure of the continuation procedure (the
/// state's `aux`) over what it holds. The frames are kept as values: each
/// frame's link as an offset from the first (or -1, for the last, whose
/// link and return address are those of whoever gives the continuation a
/// value), its return address as a fixnum, its slots as they are.
fn capture(rt: &mut fixpt_runtime::Runtime, st: &DState, frames: &[(u64, u64)], end: u64, whole: bool) -> Value {
    let base = st.fp;
    let mut words = Vec::new();
    for &(fp, stop) in frames.iter().take_while(|&&(fp, _)| fp < end) {
        let link = word(fp);
        words.push(Value::fixnum(if link > fp && link < end { (link - base) as i64 } else { -1 }));
        words.push(Value::fixnum(word(fp + 8) as i64));
        // What the frame's stack map does not trace, dead or not a value,
        // is kept as the fixnum 0: the vector is traced. (A control
        // frame's marker is where the map would be: all of it is kept.)
        let head = Value(word(fp + 16));
        let map = if head.is_fixnum() { head.as_fixnum() as u64 } else { u64::MAX };
        words.extend((fp + 16..stop).step_by(8).enumerate().map(|(j, at)| {
            if j == 0 || (j <= 64 && map & (1 << (j - 1)) != 0) { Value(word(at)) } else { Value::fixnum(0) }
        }));
    }
    let heap = &mut rt.heap;
    let saved = heap.vector_from(&words);
    let regions = Value::fixnum(heap.live_regions() as i64);
    let data = heap.vector_from(&[CONT_MARK, saved, Value::fixnum(st.ret_pc as i64), regions, Value::boolean(whole)]);
    native_closure(heap, Value(st.aux), &[data])
}

/// Continuation `k` given `v`: its frames put back, and the state told to
/// resume where it was taken. A whole one replaces the native stack, its
/// last frame returning where the current last one does, and ends the
/// regions entered since it was taken; a delimited one goes on top of the
/// continuation procedure's caller (the frame that procedure made is
/// where), its last frame returning to that caller.
fn reinstate(rt: &mut fixpt_runtime::Runtime, st: &mut DState, k: Value, v: Value) -> u64 {
    let heap = &mut rt.heap;
    let data = heap.bloblet_slot(k, CLOSURE_FREE0);
    let (saved, pc, regions, whole) = (heap.obj_ref(data, 1), heap.obj_ref(data, 2), heap.obj_ref(data, 3), heap.obj_ref(data, 4) == Value::TRUE);
    let n = heap.obj_len(saved);
    let (end, outer_link, outer_lr) = if whole {
        let &(last, _) = frames_of(st).last().expect("a frame");
        (st.stack_top, word(last), word(last + 8))
    } else {
        (st.fp + 16, word(st.fp), word(st.fp + 8))
    };
    let base = end - 8 * n as u64;
    if base < st.stack_limit {
        return failed(st, "stack overflow".into());
    }
    let mut at = 0;
    while at < n {
        let link = heap.obj_ref(saved, at).as_fixnum();
        let next = if link < 0 { n } else { link as usize / 8 };
        set_word(base + 8 * at as u64, if link < 0 { outer_link } else { base + link as u64 });
        set_word(base + 8 * at as u64 + 8, if link < 0 { outer_lr } else { heap.obj_ref(saved, at + 1).as_fixnum() as u64 });
        for j in at + 2..next {
            set_word(base + 8 * j as u64, heap.obj_ref(saved, j).raw());
        }
        at = next;
    }
    if whole {
        heap.region_exit(regions.as_fixnum() as usize);
    }
    (st.resume_sp, st.resume_fp, st.resume_pc, st.resume_x0) = (base, base, pc.as_fixnum() as u64, v.raw());
    0
}

/// The marks for `key` continuation `k` took, innermost first: a native
/// continuation's, from its frames; a cellular one's, from its return
/// stack's entries. None if `k` is neither.
fn marks_of(heap: &Heap, k: Value, key: Value) -> Option<Vec<Value>> {
    {
        if let Some(data) = heap.native_continuation_of(k) {
            let saved = heap.obj_ref(data, 1);
            let n = heap.obj_len(saved);
            let (mut out, mut at) = (Vec::new(), 0);
            while at < n {
                let link = heap.obj_ref(saved, at).as_fixnum();
                let next = if link < 0 { n } else { link as usize / 8 };
                if next - at == CONTROL_FRAME as usize / 8 && heap.obj_ref(saved, at + 2) == MARK_MARK && heap.obj_ref(saved, at + 3) == key {
                    out.push(heap.obj_ref(saved, at + 4));
                }
                at = next;
            }
            return Some(out);
        }
    }
    let c = heap.continuation_of(k)?;
    let rs = heap.bloblet_slot(c, fixpt_heap::layout::cellular::CONT_RS);
    let entries: Vec<Value> = (0..heap.obj_len(rs)).map(|i| heap.obj_ref(rs, i)).collect();
    let mut out = Vec::new();
    let mut i = entries.len();
    while i >= 4 {
        i -= 4;
        if entries[i] == fixpt_engine::cellular::MARK_MARK && entries[i + 1] == key {
            out.push(entries[i + 2]);
        }
    }
    Some(out)
}

/// The words of the frame from `fp` to `end` that a collection traces, as
/// runs (where each starts, and how many words). A frame of 16 bytes (a
/// stub's) has none. A procedure's frame has a stack map where the first
/// slot would be, a fixnum: the mask of its slots, from `fp + 24`, that are
/// live. A control frame has its marker there instead, and every word of
/// it after the link and return address is a value.
fn traced(fp: u64, end: u64) -> Vec<(u64, usize)> {
    let n = ((end - fp) / 8) as usize - 2;
    if n == 0 {
        return Vec::new();
    }
    let head = Value(word(fp + 16));
    if !head.is_fixnum() {
        return vec![(fp + 16, n)];
    }
    let map = head.as_fixnum() as u64;
    let mut runs: Vec<(u64, usize)> = Vec::new();
    for k in (0..n - 1).filter(|&k| k < 64 && map & (1 << k) != 0) {
        let at = fp + 24 + 8 * k as u64;
        match runs.last_mut() {
            Some((start, len)) if *start + 8 * *len as u64 == at => *len += 1,
            _ => runs.push((at, 1)),
        }
    }
    runs
}

/// The traced words of every native frame, innermost first, from the frame
/// that called out (`traced`): each frame runs from its frame pointer to
/// its caller's, the outermost to the stack's top.
fn native_frames<'a>(st: &DState) -> Vec<&'a mut [Value]> {
    let mut out = Vec::new();
    for (fp, end) in frames_of(st) {
        for (at, n) in traced(fp, end) {
            // SAFETY: words of a frame on the native stack that its code
            // wrote as values (its stack map says which), not overlapping
            // any other frame's.
            out.push(unsafe { std::slice::from_raw_parts_mut(at as *mut Value, n) });
        }
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

