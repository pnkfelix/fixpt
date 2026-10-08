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
use fixpt_heap::layout::cellular::{CLOSURE_FREE0, CLOSURE_WORD, GLOBAL_FIELDS, GLOBAL_WRITES, ROUTINES, WORD_CELL0, WORD_TWIN};
use fixpt_heap::layout::regcode::OPS;
use fixpt_heap::{Heap, Value};
use std::collections::HashMap;
use std::mem::offset_of;

mod reps;
use reps::{Convert, RawOp, Rep};

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
    /// The heap's card table, biased (`Heap::card_table_address`), for the
    /// write barrier.
    cards: u64,
    /// Set by a call of what is not native code that came back with an
    /// abort to a prompt in these frames: `common_foreign` resumes there.
    foreign_resume: u64,
    /// The heap's table of each region's current chunk, `[fill, end]` by
    /// handle (`Heap::region_table_address`), for `rcons` made inline.
    region_table: u64,
    /// REG1…REG8, the closure, the link and `RESULT`, kept here around a
    /// call-out that never collects (`Callout::Pure`, `Box`, `Unbox`): as
    /// they are, raw or not, since nothing moves.
    kept: [u64; 12],
    /// The stack cache (`docs/research/deep-recursion.md`): the rest of
    /// this run's frames, older than any on the stack, copied into the
    /// heap as a chain of chunks (`CH_*`): the chunk (or `#f`), where in it
    /// the next frame starts, and where that frame resumes; and the most
    /// words a run's frames may take.
    cont: u64,
    cont_at: u64,
    cont_pc: u64,
    max_words: u64,
    /// What the run's outermost frame links to and returns to: the
    /// trampoline's frame and its return.
    bottom_link: u64,
    bottom_ret: u64,
    /// The machine's underflow and overflow routines, where they run.
    underflow: u64,
    overflow: u64,
    /// What the stack cache did (`StackStats`).
    stats: StackStats,
    /// From an overflow's site: which registers its procedure's entry holds
    /// values in (`overflow_info`), and its code bloblet, kept alive and
    /// where they are by the collection the overflow makes.
    overflow_info: u64,
    overflow_code: u64,
}

/// What the stack cache did: overflows and collections, and the frames and
/// words they copied into the heap; underflows (and aborts and
/// continuations put back), and the frames they restored.
#[derive(Default, Clone, Copy, Debug, PartialEq)]
pub struct StackStats {
    pub overflows: u64,
    pub collection_flushes: u64,
    pub frames_flushed: u64,
    pub words_flushed: u64,
    pub underflows: u64,
    pub frames_restored: u64,
}

impl std::ops::AddAssign for StackStats {
    fn add_assign(&mut self, o: StackStats) {
        self.overflows += o.overflows;
        self.collection_flushes += o.collection_flushes;
        self.frames_flushed += o.frames_flushed;
        self.words_flushed += o.words_flushed;
        self.underflows += o.underflows;
        self.frames_restored += o.frames_restored;
    }
}

/// What this thread's stack caches have done, every run so far.
pub fn stack_stats() -> StackStats {
    STATS.with(|s| s.get())
}

/// The traps this code raises, by code.
const TRAPS: [&str; 6] = ["", "out of fuel", "stack overflow", "a primitive failed", "car or cdr of a non-pair", "division by zero"];
const OUT_OF_FUEL: u32 = 1;
const STACK_OVERFLOW: u32 = 2;
const PRIM_FAILED: u32 = 3;
const NOT_A_PAIR: u32 = 4;
const DIVIDED_BY_ZERO: u32 = 5;

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
    /// `rest`: the list of the arguments a variadic procedure was called
    /// with, which its `vargs` put in the state.
    Rest,
    /// A runtime primitive of `n` arguments that never collects
    /// (`fixpt_runtime::never_collects`), from `prim1`, `prim2` or
    /// `prim2imm`: no collection first, the registers kept in the state.
    Pure { p: usize, n: usize },
    /// An `i64` (signed) or `u64`'s raw 64 bits (argument 0, not a value)
    /// as the integer it is, a bignum past a fixnum (`reps`).
    Box { signed: bool },
    /// An exact integer's low 64 bits, raw (0 for anything else).
    Unbox,
    /// An `f64`'s bits (argument 0, not a value) as a flonum, where the
    /// inline allocation had no room.
    BoxF64,
    /// The stack cache's underflow (`common_underflow`): frames restored
    /// from the chain. No collection: the registers are kept raw.
    Underflow,
    /// Its overflow (`common_overflow`): the run's frames but the newest
    /// copied into the heap, that one moved to the cache's top. No
    /// collection, as for `Underflow`.
    Overflow,
}

impl Callout {
    fn arity(self) -> usize {
        match self {
            Callout::Cons | Callout::FieldRef | Callout::Abort | Callout::Reinstate | Callout::FirstMark | Callout::MarksOf => 2,
            Callout::Capture { whole } => if whole { 1 } else { 2 },
            Callout::CurrentMarks | Callout::Box { .. } | Callout::Unbox | Callout::BoxF64 => 1,
            Callout::Foreign | Callout::ClosureAny | Callout::Rest | Callout::Underflow | Callout::Overflow => 0,
            Callout::Prim { n, .. } | Callout::Pure { n, .. } | Callout::Closure { n } | Callout::RegionClosure { n } => n,
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
    /// An abort that found no prompt in the native code running, and its
    /// value: the call traps, and the caller looks further.
    static ABORTED: std::cell::Cell<Option<(Value, Value)>> = const { std::cell::Cell::new(None) };
    /// While native code has called out to run cellular code: how to run
    /// native code, and the native stack's pointer as it called out, below
    /// which a native call from that cellular code runs (`call_native`),
    /// the machine being in use.
    static CALLED_OUT: std::cell::Cell<Option<(Runner, u64)>> = const { std::cell::Cell::new(None) };
    /// The run of native code innermost, if one is running.
    static RUNNING: std::cell::Cell<Option<Runner>> = const { std::cell::Cell::new(None) };
    /// What this thread's stack caches have done (`stack_stats`).
    static STATS: std::cell::Cell<StackStats> = std::cell::Cell::new(StackStats::default());
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
    underflow: u64,
    overflow: u64,
    table: u64,
    /// The stack cache's size, and the most its chain may hold, in words.
    cache_words: u64,
    max_words: u64,
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
    crate::symbols::note(heap.code_exec_address(blob), bytes.len(), "native convention: an adapter");
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
    let fuel = rt.word_fuel.min(u64::MAX >> 1);
    let r = match CALLED_OUT.with(|c| c.get()) {
        Some((runner, sp)) => {
            let top = (sp - 16) & !15;
            if top < rt.heap.native_stack().0 + 2 * STACK_SLACK {
                return Err(fail("stack overflow".into()));
            }
            run(&runner, rt, p, args, fuel, top)
        }
        None => with_machine(|m| m.call(rt, p, args, fuel)).map_err(fail)?,
    };
    r.map_err(|t| match (take_thrown(), ABORTED.with(|a| a.take())) {
        (Some((k, v)), _) => fixpt_runtime::NativeExit::Throw { k, v },
        (None, Some((tag, v))) => fixpt_runtime::NativeExit::Abort { tag, v },
        (None, None) => fail(t.what),
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

/// The native stack is the heap's (`Heap::native_stack`), at the nursery's
/// top; a run's stack cache is part of it, with room below its limit for
/// the frame that finds it has passed it, and a chunk's start.
/// The most a stack cache may be.
const MOST_CACHE_WORDS: u64 = 1 << 22;
const STACK_SLACK: u64 = 64 * 1024;

/// The stack cache's size by default, in words: small, since every
/// collection flushes all of it (Larceny's, `docs/research/
/// deep-recursion.md`); and the most words a run's frames may take in all:
/// 2^28 (2 GB).
/// `FIXPT_NATIVE_STACK_CACHE` and `FIXPT_NATIVE_STACK_MAX` (words) say
/// otherwise.
const CACHE_WORDS: u64 = 1 << 20;
const MAX_STACK_WORDS: u64 = 1 << 28;

fn stack_words_wanted() -> (u64, u64) {
    let get = |k: &str, d: u64| std::env::var(k).ok().and_then(|v| v.parse().ok()).unwrap_or(d);
    (get("FIXPT_NATIVE_STACK_CACHE", CACHE_WORDS).clamp(1024, MOST_CACHE_WORDS), get("FIXPT_NATIVE_STACK_MAX", MAX_STACK_WORDS))
}

/// Restoring frames from the chain: at least one, and on until this many
/// words, so that each underflow is worth its call-out (Hieb, Dybvig and
/// Bruggeman's copy bound).
const RESTORE_WORDS: usize = 256;

/// A chunk of the stack cache's chain, a vector: the next chunk and where
/// in it the next frame starts (`#f` and 0 at the chain's end); the words
/// of frames from there on; then frames, each as it was on the stack, its
/// link its size (a fixnum), its second word a fixnum (a return address, a
/// landing, or 0), and its words from the third on those its stack map says
/// are dead the fixnum 0. A chunk's last frame's second word is where the
/// next resumes.
const CH_NEXT: usize = 0;
const CH_NEXT_AT: usize = 1;
const CH_REST: usize = 2;
const CH_FRAMES: usize = 3;
/// About the most words of frames a chunk holds: so that a chain mostly
/// restored keeps little more than it needs alive.
const CHUNK_WORDS: usize = 1 << 12;

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
    /// A field loaded from further than `ldr`'s 19 bits reach: the code is
    /// refused (`finish`), and the procedure runs as cellular code.
    too_far: bool,
}

impl Asm {
    fn new() -> Asm {
        Asm { code: Vec::new(), labels: Vec::new(), fixups: Vec::new(), too_far: false }
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
    /// Whether a branch so far goes to `l`.
    fn used(&self, l: Label) -> bool {
        self.fixups.iter().any(|(_, x, _)| x.0 == l.0)
    }
    /// A branch of kind `f` to `l`.
    fn to(&mut self, l: Label, f: Fix) {
        self.fixups.push((self.code.len(), l, f));
        self.code.push(NOP);
    }
    fn finish(mut self) -> Result<Vec<u32>, String> {
        // Too long for what a branch or a load reaches (`b.cond`, `adr`
        // and `ldr` have ±2^18 instructions): refused, not a panic, so
        // that the procedure runs as cellular code, saying why (PLAN.md B1).
        let too_far = || format!("its code, {} instructions, is too long for a branch or load to reach across", self.code.len());
        if self.too_far {
            return Err(too_far());
        }
        for &(at, l, f) in &self.fixups {
            let to = self.labels[l.0].ok_or("a label never placed")? as i64;
            let reach = if matches!(f, Fix::B | Fix::Bl) { 1i64 << 25 } else { 1i64 << 18 };
            if !(-reach..reach).contains(&(to - at as i64)) {
                return Err(too_far());
            }
        }
        for (at, l, f) in std::mem::take(&mut self.fixups) {
            let to = self.labels[l.0].ok_or("a label never placed")?;
            let d = to as i64 - at as i64;
            self.code[at] = match f {
                // A branch to a `ret` is that `ret`: a fast path that joins
                // the slow one only to return (nothing counts a code's
                // returns; a return address is a call's).
                Fix::B if self.code[to] == ret() => ret(),
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
    /// A global's procedure, which may be called through its cell instead.
    global: bool,
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
    /// Where a return off the stack cache's top goes, its frames restored
    /// from the chain; and where a procedure whose frame passed the
    /// cache's limit goes, the rest flushed into the heap.
    underflow: Offset,
    overflow: Offset,
    cache_words: u64,
    max_words: u64,
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
        // 1: a closure made (`common_closure`); 2 and 3: the stack cache's
        // underflow and overflow (`common_underflow`, `common_overflow`).
        let callouts = vec![Callout::Foreign, Callout::ClosureAny, Callout::Underflow, Callout::Overflow];
        let code = common_foreign(0);
        let foreign = space.alloc(4 * code.len(), 16).ok_or("no room for the common foreign call")?;
        space.write_code(foreign, &code);
        space.flush(foreign, 4 * code.len());
        let code = common_closure(1);
        let closure = space.alloc(4 * code.len(), 16).ok_or("no room for the common closure")?;
        space.write_code(closure, &code);
        space.flush(closure, 4 * code.len());
        let code = common_underflow(2);
        let underflow = space.alloc(4 * code.len(), 16).ok_or("no room for the underflow")?;
        space.write_code(underflow, &code);
        space.flush(underflow, 4 * code.len());
        let code = common_overflow(3);
        let overflow = space.alloc(4 * code.len(), 16).ok_or("no room for the overflow")?;
        space.write_code(overflow, &code);
        space.flush(overflow, 4 * code.len());
        let stub = |at: usize, len: usize, what: &str| crate::symbols::note(space.exec_addr(at), 4 * len, &format!("native convention: {what}"));
        stub(underflow, common_underflow(2).len(), "stack cache underflow");
        stub(overflow, common_overflow(3).len(), "stack cache overflow");
        stub(entry, trampoline().len(), "trampoline");
        stub(mark_ret, pop_mark.len(), "a mark's return");
        stub(trap_stub, common_trap().len(), "common trap");
        stub(foreign, common_foreign(0).len(), "common foreign call");
        stub(closure, common_closure(1).len(), "common closure");
        let (cache_words, max_words) = stack_words_wanted();
        Ok(DirectMachine {
            space,
            entry,
            mark_ret,
            trap_stub,
            foreign,
            closure,
            underflow,
            overflow,
            cache_words,
            max_words,
            callouts,
        })
    }

    /// The stack cache's size, and the most words a run's frames may take
    /// in all (on the stack and in the heap), past which it overflows.
    pub fn set_stack_words(&mut self, cache: u64, max: u64) {
        self.cache_words = cache.clamp(1024, MOST_CACHE_WORDS);
        self.max_words = max;
    }

    /// Compile `closure`'s procedure, and every procedure it calls or
    /// makes closures of, to code in the native convention, each in a code
    /// bloblet of its own: what it compiled, the first first; or why it
    /// could not.
    pub fn compile(&mut self, heap: &mut Heap, closure: Value) -> Result<Vec<(String, Compiled)>, String> {
        // A global's procedure that cannot be compiled is called as what is
        // not native code, and the rest compiled again without it.
        let mut refused = std::collections::HashSet::new();
        let (procs, first, free) = loop {
            let mut c = Compiling { heap: &*heap, procs: Vec::new(), by_word: HashMap::new(), queue: Vec::new(), callouts: &mut self.callouts, resume: None, refused };
            let (word, free) = c.closure_parts(closure).ok_or("not a closure of cellular code")?;
            let first = c.proc_of(word)?;
            let mut failed = None;
            while let Some(p) = c.queue.pop() {
                if let Err(e) = c.procedure(p) {
                    failed = Some((p, e));
                    break;
                }
            }
            match failed {
                None => break (std::mem::take(&mut c.procs), first, free),
                Some((p, e)) if p == first || !c.procs[p].global => return Err(e),
                Some((p, _)) => {
                    refused = std::mem::take(&mut c.refused);
                    refused.insert(c.procs[p].word.raw());
                }
            }
        };
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
            if crate::symbols::enabled() {
                crate::symbols::note(heap.code_exec_address(blob), bytes.len(), &format!("native {}", p.name));
            }
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
        // The heap's native stack (`Heap::native_stack`), with room at its
        // top for a chunk's trailer (`flush_in_place`).
        let top = (rt.heap.native_stack().1 - 16) & !15;
        run(&self.runner(), rt, p, args, fuel, top)
    }

    fn runner(&self) -> Runner {
        Runner {
            entry: self.space.exec_addr(self.entry) as u64,
            mark_ret: self.space.exec_addr(self.mark_ret) as u64,
            trap_stub: self.space.exec_addr(self.trap_stub) as u64,
            foreign: self.space.exec_addr(self.foreign) as u64,
            closure: self.space.exec_addr(self.closure) as u64,
            underflow: self.space.exec_addr(self.underflow) as u64,
            overflow: self.space.exec_addr(self.overflow) as u64,
            table: self.callouts.as_ptr() as u64,
            cache_words: self.cache_words,
            max_words: self.max_words,
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
    // The count, for a variadic procedure; past 8, the eighth a list of
    // the rest (Larceny's convention).
    let count = args.len() as u64;
    let packed;
    let args = if args.len() > 8 {
        let rest = rt.heap.list_from(&args[7..]);
        packed = [&args[..7], &[rest]].concat();
        &packed[..]
    } else {
        args
    };
    THROWN.with(|t| t.set(None));
    let mut st = DState {
        stack_top: top,
        // The cache: this run's part of the stack, below which a frame's
        // entry flushes the rest into the heap.
        stack_limit: (rt.heap.native_stack().0 + STACK_SLACK).max(top.saturating_sub(8 * r.cache_words)),
        cont: Value::FALSE.raw(),
        max_words: r.max_words,
        underflow: r.underflow,
        overflow: r.overflow,
        fuel,
        callout: callout as *const () as u64,
        rt: rt as *mut fixpt_runtime::Runtime as u64,
        table: r.table,
        top: rt.heap.top_address() as u64,
        words: rt.heap.words_address() as u64,
        alloc_limit: rt.heap.inline_limit() as u64,
        regions: Value::fixnum(rt.heap.live_regions() as i64).raw(),
        cards: rt.heap.card_table_address() as u64,
        region_table: rt.heap.region_table_address() as u64,
        ..DState::default()
    };
    for (i, a) in args.iter().enumerate() {
        st.args[i] = a.raw();
    }
    st.nargs = count;
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
    STATS.with(|s| {
        let mut t = s.get();
        t += st.stats;
        s.set(t);
    });
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
    // The count, for a variadic procedure (`vargs`).
    a.e(ldr(X9, ST, st_off(offset_of!(DState, nargs))));
    // What the outermost frame links and returns to, for the stack cache
    // to give a frame it restores last.
    let back = a.label();
    a.e(str(FRAME, ST, st_off(offset_of!(DState, bottom_link))));
    a.to(back, Fix::Adr(X17));
    a.e(str(X17, ST, st_off(offset_of!(DState, bottom_ret))));
    a.e(blr(X16));
    a.bind(back);
    a.e(str(FUEL, ST, st_off(offset_of!(DState, fuel))));
    leave(&mut a);
    a.finish().expect("labels bound")
}

/// The stack cache's underflow: where the last frame on the cache returns
/// (its return address this routine's), its value in `RESULT` (REG1…REG8
/// kept too): call-out `n` (`Callout::Underflow`) restores frames from the
/// chain onto the cache, and there, the innermost's code resumes. One for
/// the machine.
fn common_underflow(n: usize) -> Vec<u32> {
    let mut a = Asm::new();
    let kept = offset_of!(DState, kept) as u32;
    for r in 0..9u32 {
        a.e(str(r as Reg, ST, kept + 8 * r));
    }
    call_out(&mut a, n);
    a.e(ldr(X9, ST, st_off(offset_of!(DState, trap))));
    let failed = a.label();
    a.e(cmp_imm(X9, 0));
    a.to(failed, Fix::If(Cond::Ne));
    for r in 0..9u32 {
        a.e(ldr(r as Reg, ST, kept + 8 * r));
    }
    a.e(ldr(X9, ST, st_off(offset_of!(DState, resume_sp))));
    a.e(add_imm(SP, X9, 0));
    a.e(ldr(FRAME, ST, st_off(offset_of!(DState, resume_fp))));
    a.e(ldr(X16, ST, st_off(offset_of!(DState, resume_pc))));
    a.e(br(X16));
    a.bind(failed);
    a.e(movz(X9, PRIM_FAILED, 0));
    a.e(ldr(X16, ST, st_off(offset_of!(DState, trap_stub))));
    a.e(br(X16));
    a.finish().expect("labels bound")
}

/// The stack cache's overflow: from a procedure's entry whose frame, just
/// pushed, passed the cache's limit (by `bl`, from the site's stub, whose
/// return is where the entry goes on; its code bloblet in X16, which of its
/// registers hold values in X17, `overflow_info`): every register it may
/// need kept, call-out `n` (`Callout::Overflow`) flushes the run's other
/// frames where they are, collects, and moves this one to the cache's top;
/// back with the stack and frame where it is now. One for the machine.
fn common_overflow(n: usize) -> Vec<u32> {
    let mut a = Asm::new();
    let kept = offset_of!(DState, kept) as u32;
    for r in 0..11u32 {
        a.e(str(r as Reg, ST, kept + 8 * r));
    }
    a.e(str(LINK, ST, kept + 88));
    a.e(str(X16, ST, st_off(offset_of!(DState, overflow_code))));
    a.e(str(X17, ST, st_off(offset_of!(DState, overflow_info))));
    call_out(&mut a, n);
    a.e(ldr(LINK, ST, kept + 88));
    a.e(ldr(X9, ST, st_off(offset_of!(DState, trap))));
    let failed = a.label();
    a.e(cmp_imm(X9, 0));
    a.to(failed, Fix::If(Cond::Ne));
    a.e(ldr(X9, ST, st_off(offset_of!(DState, resume_sp))));
    a.e(add_imm(SP, X9, 0));
    a.e(ldr(FRAME, ST, st_off(offset_of!(DState, resume_fp))));
    for r in 0..11u32 {
        a.e(ldr(r as Reg, ST, kept + 8 * r));
    }
    a.e(ret());
    a.bind(failed);
    a.e(movz(X9, PRIM_FAILED, 0));
    a.e(ldr(X16, ST, st_off(offset_of!(DState, trap_stub))));
    a.e(br(X16));
    a.finish().expect("labels bound")
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
    let (failed, stub, resumed) = (a.label(), a.label(), a.label());
    a.to(failed, Fix::If(Cond::Ne));
    // Back with an abort to a prompt in these frames: resumed there.
    a.e(ldr(X9, ST, st_off(offset_of!(DState, foreign_resume))));
    a.e(cmp_imm(X9, 0));
    a.to(resumed, Fix::If(Cond::Ne));
    a.e(ldp_post(FRAME, LINK, SP, 16));
    a.e(ret());
    a.bind(resumed);
    a.e(str(XZR, ST, st_off(offset_of!(DState, foreign_resume))));
    resume(&mut a);
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
    /// Globals' procedures that could not be compiled (a word's raw
    /// value): called through their cells, as what is not native code.
    refused: std::collections::HashSet<u64>,
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
        self.procs.push(Proc { word: Value::FALSE, rw: Value::FALSE, name: "continuation".into(), arity: 1, fields: vec![Field::Myself, Field::Const(Value::FALSE)], len: code.len(), code, global: false });
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
        // A variadic procedure's (`vargs`) arity is none: any number.
        let variadic = h.bloblet_slot(rw, WORD_CELL0).as_fixnum() as usize == fixpt_heap::layout::regcode::op("vargs");
        let arity = if variadic { usize::MAX } else { h.bloblet_slot(rw, WORD_CELL0 + 1).as_fixnum() as usize };
        let p = self.procs.len();
        self.procs.push(Proc { word, rw, name: self.name(word), arity, fields: vec![Field::Myself, Field::Const(word)], code: Vec::new(), len: 0, global: false });
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
    /// now, as a native closure of its procedure: used while the cell has
    /// not been written since, which its uses test (`global`, `invoke`), as
    /// the code may outlive a later definition. A cell with no count of its
    /// writes is read when the code runs.
    fn global_value(&mut self, cell: Value) -> Result<Field, String> {
        let v = self.heap.bloblet_slot(cell, 2);
        // Not defined yet (a definition of itself, being compiled): what its
        // cell holds when the code runs.
        // A cellular closure of no register code (an adapter) cannot be
        // compiled: called through its cell, as what is not native code.
        if let Some((word, free)) = self.closure_parts(v)
            && self.heap.bloblet_head(cell).fields >= GLOBAL_FIELDS
            && self.name(word) != "undefined"
            && self.heap.is_register_word(self.heap.bloblet_slot(word, WORD_TWIN))
            && !self.refused.contains(&word.raw())
        {
            let q = self.proc_of(word)?;
            self.procs[q].global = true;
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
        if frame.is_some_and(|m| 24 + 8 * (m + 2) > 4080) {
            return decline("a frame too large".into());
        }
        // A frame of more slots than a fixnum's mask has bits has no stack
        // map: all its slots are traced, and cleared as it is made.
        let unmapped = frame.is_some_and(|m| m + 2 > 60);
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
                let bit = |j: usize| 1u64.checked_shl(cells[i + 1 + j].as_fixnum() as u32).unwrap_or(0);
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
        let mut map_stored: Option<u64>;
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
        // Each frame's entry past the stack cache's limit: its stub, and
        // where it comes back to.
        let mut overflows: Vec<(Label, Label)> = Vec::new();
        // Each call of a global bound when compiled whose cell holds
        // something else when the code runs: out of the way, the call
        // through the cell (with the call's stub, and where to come back).
        let mut cell_slows: Vec<(Label, Label, Label)> = Vec::new();
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
        // Where `i64` and `u64` values are raw (`reps`): the registers as
        // each instruction starts, and ends; the ways into an instruction
        // that must unbox some first, each a stub of its own.
        let prim_name = |p: usize| fixpt_runtime::PRIMITIVES.get(p).map_or("?", |d| d.name);
        let raw_refs = reps::raw_refs(&cells, &starts, &prim_name);
        let si_at: HashMap<usize, usize> = starts.iter().enumerate().map(|(si, &i)| (i, si)).collect();
        // A procedure with `int` operations gets a fixnum version first, where
        // a value tested once stays known (`reps`, `Rep::Fix`), and whose
        // tests and overflows go over to the general version, at the same
        // instruction: the registers and frame are the same in both there.
        let has_int = starts.iter().any(|&i| matches!(op_at(i), "op2" | "op2imm") && reps::int_routine(cells[i + 1].as_fixnum() as usize));
        let live = reps::live_in(&cells, &starts, &prim_name);
        let labels_g = labels;
        let labels_f: Vec<Label> = (0..=cells.len()).map(|_| a.label()).collect();
        let versions: &[bool] = if has_int { &[true, false] } else { &[false] };
        let mut edge_stubs: Vec<(Label, Vec<(usize, Rep)>, Vec<usize>, Label, Label)> = Vec::new();
        let mut int_slows: Vec<IntSlow> = Vec::new();
        for &fast in versions {
        let labels = if fast { &labels_f } else { &labels_g };
        let (reps_in, reps_out) = reps::reps_of(&cells, &starts, &prim_name, fast);
        let mut src = RESULT;
        let mut pending: Option<Field> = None;
        // The global the pending call was bound to as compiled: its cell,
        // and how many times it had been written then.
        let mut bound: Option<(Value, Value)> = None;
        map_stored = None;
        let mut edge = |a: &mut Asm, from: usize, to: usize| -> Label {
            let (unbox, check) = match si_at.get(&to) {
                Some(&t) => (
                    reps::unboxes(&reps_out[from], &reps_in[t]),
                    if fast { reps::checks(&reps_out[from], &reps_in[t], &live[t]) } else { vec![] },
                ),
                None => (vec![], vec![]),
            };
            if unbox.is_empty() && check.is_empty() {
                return labels[to];
            }
            let l = a.label();
            edge_stubs.push((l, unbox, check, labels[to], labels_g[to]));
            l
        };
        let mut si = 0;
        while si < starts.len() {
            let i = starts[si];
            // Falling in from the instruction before, the registers it
            // leaves as values that are raw here unboxed; in the fixnum
            // version, those it leaves unknown that are known here tested.
            if si > 0 && !matches!(op_at(starts[si - 1]), "branch" | "return" | "tailinvoke") {
                for (r, rep) in reps::unboxes(&reps_out[si - 1], &reps_in[si]) {
                    unbox_to(&mut a, self.callouts, r as Reg, rep);
                }
                if fast {
                    for r in reps::checks(&reps_out[si - 1], &reps_in[si], &live[si]) {
                        check_fixnum(&mut a, r as Reg, labels_g[i]);
                    }
                }
            }
            si += 1;
            a.bind(labels[i]);
            let op = op_at(i);
            {
                let o = |j: usize| cells[i + 1 + j];
                let mut reps = reps_in[si - 1];
                let first = reps::step(op, &o, &prim_name, raw_refs[si - 1], fast, &mut reps);
                // `RESULT`, where a `reg` just before left it in its register
                // (`src`), is tested there.
                convert(&mut a, self.callouts, &first, labels_g[i], src);
            }
            if target[i] {
                map_stored = None;
            }
            // Before what may collect, in a frame: the slots live after it,
            // the code bloblet's, and the closure's if the code reads it.
            if let Some(m) = frame
                && framed[i]
                && (matches!(op, "prim" | "cellular" | "lambda" | "invokeself") || op == "invoke")
            {
                let map = if unmapped { u64::MAX } else { live_out[si - 1] | 1 << m | if captures { 1 << (m + 1) } else { 0 } };
                if map_stored != Some(map) {
                    a.es(&mov_imm64(X16, Value::fixnum(if unmapped { -1 } else { map as i64 }).raw()));
                    a.e(str(X16, FRAME, 16));
                    map_stored = Some(map);
                }
            }
            let o = |j: usize| cells[i + 1 + j];
            let k = |v: Value| v.as_fixnum() as usize;
            let reg = |v: Value| v.as_fixnum() as Reg;
            match op {
                "args" => {}
                // Entered with any number of arguments, their count in X9:
                // it and the registers into the state, for `rest` to list.
                "vargs" => {
                    a.e(str(X9, ST, st_off(offset_of!(DState, nargs))));
                    let args = offset_of!(DState, args) as u32;
                    for j in 0..8u32 {
                        a.e(str(1 + j as Reg, ST, args + 8 * j));
                    }
                }
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
                    let writes = self.heap.bloblet_slot(cell, GLOBAL_WRITES);
                    let g = self.global_value(cell).map_err(|e| format!("`{name}` calls {e}"))?;
                    if called(i).is_some() {
                        if !matches!(g, Field::Cell(_)) {
                            bound = Some((cell, writes));
                        }
                        pending = Some(g);
                    } else {
                        // What the cell holds when the code runs; the
                        // native closure bound, where the cell has not been
                        // written since this code was compiled: a later
                        // definition is seen.
                        let fc = self.field(p, Field::Cell(cell));
                        ldr_field(&mut a, X9, fc);
                        a.e(ldur(RESULT, X9, field_off(2)));
                        if !matches!(g, Field::Cell(_)) {
                            let other = a.label();
                            a.e(ldur(X11, X9, field_off(GLOBAL_WRITES)));
                            a.es(&mov_imm64(X16, writes.raw()));
                            a.e(cmp(X11, X16));
                            a.to(other, Fix::If(Cond::Ne));
                            // A procedure's code alone is no value: its
                            // closure, over nothing.
                            let f = match g {
                                Field::Code(q) => self.field(p, Field::Closure(q, vec![])),
                                g => self.field(p, g),
                            };
                            ldr_field(&mut a, RESULT, f);
                            a.bind(other);
                        }
                    }
                }
                // Always the test, which the code runs, as this code may
                // outlive a later definition of the global: how many times
                // the cell has been written, against how many when the code
                // was compiled.
                "global-guard" => {
                    let (cell, n, to) = (o(0), o(1), (i as i64 + 4 + o(2).as_fixnum()) as usize);
                    let fc = self.field(p, Field::Cell(cell));
                    ldr_field(&mut a, X9, fc);
                    a.e(ldur(X11, X9, field_off(GLOBAL_WRITES)));
                    a.es(&mov_imm64(X16, n.raw()));
                    a.e(cmp(X11, X16));
                    let l = edge(&mut a, si - 1, to);
                    a.to(l, Fix::If(Cond::Ne));
                }
                "setglbl" => {
                    let f = self.field(p, Field::Cell(o(0)));
                    ldr_field(&mut a, X9, f);
                    a.e(stur(RESULT, X9, field_off(2)));
                    // One more write, for the guards (`global-guard`).
                    a.e(ldur(X16, X9, field_off(GLOBAL_WRITES)));
                    a.e(add_imm(X16, X16, Value::fixnum(1).raw() as u32));
                    a.e(stur(X16, X9, field_off(GLOBAL_WRITES)));
                    a.es(&card_mark(X9, field_off(2), ST, st_off(offset_of!(DState, cards)), X16, X17));
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
                    Some(j) if matches!(op_at(j), "op2" | "op2imm") && !matches!(reps_in[si - 1][k(o(0)).min(8)], Rep::Raw { .. }) => {
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
                    // One `stp` reaches 504 bytes; past that, `sub` first.
                    if size <= 504 {
                        a.e(stp_pre(FRAME, LINK, SP, -size));
                    } else {
                        a.e(sub_imm(SP, SP, size as u32));
                        a.e(stp(FRAME, LINK, SP, 0));
                    }
                    a.e(add_imm(FRAME, SP, 0));
                    // Past the stack cache's limit: the rest flushed into
                    // the heap, and this frame moved to the cache's top
                    // (`common_overflow`).
                    a.e(cmp_sp(LIMIT));
                    let (over, back) = (a.label(), a.label());
                    a.to(over, Fix::If(Cond::Lo));
                    a.bind(back);
                    overflows.push((over, back));
                    map_stored = None;
                    if unmapped {
                        for off in (24..size as u32).step_by(8) {
                            a.e(str(XZR, FRAME, off));
                        }
                    } else {
                        let unwritten = live_out[si - 1];
                        for k in (0..64).filter(|k| unwritten & (1 << k) != 0) {
                            a.e(str(XZR, FRAME, 24 + 8 * k));
                        }
                    }
                    ldr_field(&mut a, X9, 1);
                    a.e(str(X9, FRAME, self_slot.expect("a frame")));
                    if captures {
                        a.e(str(CLO, FRAME, clo_slot.expect("a frame")));
                    }
                }
                "pop" => {
                    let size = size.expect("a frame") as i64;
                    if size <= 504 {
                        a.e(ldp_post(FRAME, LINK, SP, size));
                    } else {
                        a.e(ldp(FRAME, LINK, SP, 0));
                        a.e(add_imm(SP, SP, size as u32));
                    }
                }
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
                    // A list may be `nil`: `car` of it traps.
                    r @ ("pair-car" | "pair-cdr") => {
                        a.e(and_low(X16, RESULT, 3));
                        a.e(cmp_imm(X16, fixpt_heap::value::TAG_PAIR as u32));
                        trap(&mut a, &mut stubs, NOT_A_PAIR, Cond::Ne);
                        a.e(ldur(RESULT, RESULT, if r == "pair-car" { -1 } else { 7 }));
                    }
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
                    let fast_int = fast && reps::int_routine(k(o(0)));
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
                    // Ints: fixnums here; a bignum, or a sum past a fixnum,
                    // the runtime's, called with no collection, out of the
                    // way (`IntSlow`; PLAN.md, Q2).
                    let prim = match r {
                        "int-add" => Some("%fx26-add"),
                        "int-sub" => Some("%fx26-sub"),
                        "int-less" => Some("%fx26-int-less"),
                        "int-eq" => Some("%fx26-int-eq"),
                        "eq" => None,
                        _ => return decline(format!("{op} {r}")),
                    }
                    .map(|n| fixpt_runtime::PRIMITIVES.iter().position(|d| d.name == n).expect("a primitive"))
                    // `=` with a fixnum is the same word: a bignum is never
                    // one that would fit a fixnum. In the fixnum version,
                    // the operands are known fixnums: no test, no slow path.
                    .filter(|_| !fast_int && !(r == "int-eq" && op == "op2imm" && o(1).is_fixnum()));
                    let (entry, back) = (a.label(), a.label());
                    let mut slow = IntSlow { entry, overflow: None, back, x, y: other, imm: small, into: d, prim: 0, sub: r == "int-sub", branch: None };
                    if prim.is_some() {
                        if small.is_some() || other == x {
                            a.e(tst_low(x, 3));
                        } else {
                            a.e(orr(X13, x, other));
                            a.e(tst_low(X13, 3));
                        }
                        a.to(entry, Fix::If(Cond::Ne));
                    }
                    // The sum in its register, which the slow path undoes to
                    // the operand if it is that; in a scratch one if it is the
                    // other operand's, which could not be.
                    // (In the fixnum version, not over an operand either: an
                    // overflow goes over to the general version of this
                    // instruction, which does it again.)
                    let dst = if (small.is_none() && d == other) || (fast_int && d == x) { X13 } else { d };
                    match (r, small) {
                        ("int-add", Some(n)) => a.e(adds_imm(dst, x, n)),
                        ("int-add", None) => a.e(adds(dst, x, other)),
                        ("int-sub", Some(n)) => a.e(subs_imm(dst, x, n)),
                        ("int-sub", None) => a.e(subs(dst, x, other)),
                        (_, Some(n)) => a.e(cmp_imm(x, n)),
                        (_, None) => a.e(cmp(x, other)),
                    }
                    let cond = if r == "int-less" { Cond::Lt } else { Cond::Eq };
                    match r {
                        "int-add" | "int-sub" if fast_int => {
                            a.to(labels_g[i], Fix::If(Cond::Vs));
                            if dst != d {
                                a.e(mov(d, dst));
                            }
                        }
                        "int-add" | "int-sub" => {
                            let ov = a.label();
                            a.to(ov, Fix::If(Cond::Vs));
                            if dst != d {
                                a.e(mov(d, dst));
                            }
                            slow.overflow = Some(ov);
                        }
                        // A test that only a branch reads: the branch on the
                        // flags, with no boolean made (on the slow path, on
                        // the boolean the call made).
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
                                let taken_if_true = op_at(j) == "brancht";
                                let cond = match (taken_if_true, cond) {
                                    (false, Cond::Eq) => Cond::Ne,
                                    (false, _) => Cond::Ge,
                                    (true, c) => c,
                                };
                                let l = edge(&mut a, si, to);
                                a.to(l, Fix::If(cond));
                                slow.branch = Some((l, taken_if_true));
                                slow.into = RESULT;
                                si += 1;
                            }
                            _ => {
                                a.es(&mov_imm64(X9, Value::TRUE.raw()));
                                a.es(&mov_imm64(X17, Value::FALSE.raw()));
                                a.e(csel(RESULT, X9, X17, cond));
                                slow.into = RESULT;
                            }
                        },
                    }
                    if let Some(p) = prim {
                        slow.prim = p;
                        int_slows.push(slow);
                    }
                    a.bind(back);
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
                    a.es(&card_mark(RESULT, off, ST, st_off(offset_of!(DState, cards)), X16, X17));
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
                        for j in 0..c.arity().min(8) {
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
                        // A control frame may pass the cache's limit by
                        // half the slack: the next procedure's frame
                        // flushes it with the rest.
                        a.e(add_imm_pages(X16, SP, (STACK_SLACK / 2 / 4096) as u32));
                        a.e(cmp(X16, LIMIT));
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
                // A primitive that never collects, on `RESULT` and `REGk` or
                // a constant: in line, where its fast path can; else a
                // call-out with no collection, the registers kept around it.
                "prim1" | "prim2" | "prim2imm" => {
                    let pn = k(o(0));
                    let name = fixpt_runtime::PRIMITIVES.get(pn).map_or("?", |d| d.name);
                    if !fixpt_runtime::never_collects(name) {
                        return decline(format!("`{op}` of `{name}`, which may collect"));
                    }
                    // An `i64` or `u64` operation: its operands raw where it
                    // takes them so (unboxed already, as `reps` said), a
                    // constant made so here.
                    // An element only `f64` operations use: its bits.
                    if name == "%fx26-flatarray-ref" && raw_refs[si - 1] {
                        let y = if op == "prim2" { reg(o(1)) } else {
                            a.es(&mov_imm64(X17, o(1).raw()));
                            X17
                        };
                        let (slow, done) = (a.label(), a.label());
                        flat_element(&mut a, RESULT, y, slow);
                        a.e(ldr_x8(RESULT, X15, X14));
                        a.to(done, Fix::B);
                        a.bind(slow);
                        pure_call(&mut a, self.callouts, Callout::Pure { p: pn, n: 2 }, &[RESULT, y], RESULT);
                        a.e(ldr(X9, ST, st_off(offset_of!(DState, trap))));
                        a.e(cmp_imm(X9, 0));
                        trap(&mut a, &mut stubs, PRIM_FAILED, Cond::Ne);
                        unbox_f64(&mut a, RESULT);
                        a.bind(done);
                        continue;
                    }
                    if let Some(RawOp::F64 { what }) = reps::raw_op(name) {
                        match what {
                            "from-int" => f64_of_int(&mut a, self.callouts, pn),
                            "->int" => int_of_f64(&mut a, self.callouts, &mut stubs, pn),
                            _ => f64_fast(&mut a, what, if op == "prim2" { reg(o(1)) } else { RESULT }),
                        }
                        continue;
                    }
                    if let Some(RawOp::Int { signed, what }) = reps::raw_op(name) {
                        let y = match op {
                            "prim2" => reg(o(1)),
                            "prim2imm" => {
                                let v = o(1);
                                let count = matches!(what, "-shl" | "-shr");
                                if v.is_fixnum() && !count {
                                    a.es(&mov_imm64(X17, v.as_fixnum() as u64));
                                } else if v.is_fixnum() || v.raw() & 7 == 3 {
                                    a.es(&mov_imm64(X17, v.raw()));
                                } else {
                                    let f = self.field(p, Field::Const(v));
                                    ldr_field(&mut a, X17, f);
                                    if !count {
                                        unbox_reg(&mut a, self.callouts, X17);
                                    }
                                }
                                X17
                            }
                            _ => X17,
                        };
                        if what == "->int" {
                            box_reg(&mut a, self.callouts, RESULT, signed);
                        } else {
                            raw_fast(&mut a, &mut stubs, signed, what, y);
                        }
                        continue;
                    }
                    let y = match op {
                        "prim2" => reg(o(1)),
                        "prim2imm" => {
                            let v = o(1);
                            if v.is_fixnum() || v.raw() & 7 == 3 {
                                a.es(&mov_imm64(X17, v.raw()));
                            } else {
                                let f = self.field(p, Field::Const(v));
                                ldr_field(&mut a, X17, f);
                            }
                            X17
                        }
                        _ => X17,
                    };
                    let (slow, done) = (a.label(), a.label());
                    let fast = pure_fast(&mut a, name, y, slow);
                    // A fast path that never fails (`u32+` wraps) has no
                    // slow one: nothing would reach it.
                    if !fast || a.used(slow) {
                        if fast {
                            a.to(done, Fix::B);
                        }
                        a.bind(slow);
                        let n = if op == "prim1" { 1 } else { 2 };
                        pure_call(&mut a, self.callouts, Callout::Pure { p: pn, n }, &[RESULT, y][..n], RESULT);
                        a.e(ldr(X9, ST, st_off(offset_of!(DState, trap))));
                        a.e(cmp_imm(X9, 0));
                        trap(&mut a, &mut stubs, PRIM_FAILED, Cond::Ne);
                    }
                    a.bind(done);
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
                        ("cellular", Some("rest")) if k(o(1)) == 0 => Callout::Rest,
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
                    // `rcons`, likewise, in the region's current chunk, when
                    // its handle (in `x1`) has a slot in the heap's table
                    // and the chunk has room: its fill bumped by two words.
                    // Anything else calls in: `#f`, the heap's; a region
                    // with no chunk yet, or a full one (its fill and end are
                    // 0 when it has none). As the cellular machine's does.
                    if let Callout::Prim { p, n: 3 } = c
                        && fixpt_runtime::PRIMITIVES[p].name == "%region-cons"
                    {
                        a.e(tst_low(1, 3));
                        a.to(slow, Fix::If(Cond::Ne));
                        a.e(cmp_imm(1, 8 * fixpt_heap::heap::REGION_SLOTS as u32));
                        a.to(slow, Fix::If(Cond::Hs));
                        a.e(ldr(X13, ST, st_off(offset_of!(DState, region_table))));
                        a.e(add_lsl(X13, X13, 1, 1));
                        a.e(ldp(X14, X15, X13, 0));
                        a.e(add_imm(X16, X14, 2));
                        a.e(cmp(X16, X15));
                        a.to(slow, Fix::If(Cond::Hi));
                        a.e(ldr(X9, ST, st_off(offset_of!(DState, words))));
                        a.e(add_lsl(X11, X9, X14, 3));
                        a.e(stp(2, 3, X11, 0));
                        a.e(str(X16, X13, 0));
                        a.e(add_imm(RESULT, X11, fixpt_heap::value::TAG_PAIR as u32));
                        a.to(done, Fix::B);
                    }
                    // A raw `f64` to store is boxed only if the call-out
                    // must do it.
                    let raw_store = reps_in[si - 1][3] == Rep::F64;
                    if let Callout::Prim { p, n: 3 } = c
                        && fixpt_runtime::PRIMITIVES[p].name == "%fx26-flatarray-set!"
                    {
                        flat_set(&mut a, slow, done, raw_store);
                    }
                    // `int`'s bit operations of fixnums (`TODO.md` §56): of
                    // two, `and`, `ior` and `xor` are one; `not` of one, its
                    // tag's bits cleared. A bignum calls out.
                    if let Callout::Prim { p, n } = c
                        && let op @ ("%fx26-bitwise-and" | "%fx26-bitwise-ior" | "%fx26-bitwise-xor" | "%fx26-bitwise-not") =
                            fixpt_runtime::PRIMITIVES[p].name
                    {
                        if n == 2 {
                            a.e(orr(X13, 1, 2));
                            a.e(tst_low(X13, 3));
                        } else {
                            a.e(tst_low(1, 3));
                        }
                        a.to(slow, Fix::If(Cond::Ne));
                        match op {
                            "%fx26-bitwise-and" => a.e(and(RESULT, 1, 2)),
                            "%fx26-bitwise-ior" => a.e(orr(RESULT, 1, 2)),
                            "%fx26-bitwise-xor" => a.e(eor(RESULT, 1, 2)),
                            _ => {
                                a.e(sub(RESULT, XZR, 1));
                                a.e(sub_imm(RESULT, RESULT, 8));
                            }
                        }
                        a.to(done, Fix::B);
                    }
                    // A mutable bloblet of no suffix (`%make-bloblet`, `x1`
                    // its suffix's bytes, 0, else the call-out), from the
                    // free space as a pair is: its header, its fields from
                    // `x2`…, its trailer (`TODO.md` §57).
                    if let Callout::Prim { p, n } = c
                        && fixpt_runtime::PRIMITIVES[p].name == "%make-bloblet"
                        && (1..=fixpt_heap::layout::regcode::REGS).contains(&n)
                    {
                        let total = n;
                        a.e(cmp_imm(1, 0));
                        a.to(slow, Fix::If(Cond::Ne));
                        a.e(ldr(X13, ST, st_off(offset_of!(DState, top))));
                        a.e(ldr(X14, X13, 0));
                        a.e(ldr(X15, ST, st_off(offset_of!(DState, alloc_limit))));
                        a.e(add_imm(X16, X14, 1 + total as u32));
                        a.e(cmp(X16, X15));
                        a.to(slow, Fix::If(Cond::Hi));
                        a.e(ldr(X9, ST, st_off(offset_of!(DState, words))));
                        a.e(add_lsl(X11, X9, X14, 3));
                        a.e(str(X16, X13, 0));
                        let h = fixpt_heap::value::make_header(fixpt_heap::layout::kind("bloblet"), total, 0);
                        a.es(&mov_imm64(X15, h));
                        a.e(str(X15, X11, 0));
                        for j in 2..=n {
                            a.e(str(j as Reg, X11, 8 * (1 + total - j) as u32));
                        }
                        let t = fixpt_heap::layout::T_DISTANCE.put(fixpt_heap::value::TAG_TRAILER, total as u64);
                        a.es(&mov_imm64(X15, t));
                        a.e(str(X15, X11, 8 * total as u32));
                        a.e(add_imm(RESULT, X11, (8 * (1 + total) + fixpt_heap::value::TAG_BLOBLET as usize) as u32));
                        a.to(done, Fix::B);
                    }
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
                    // `%bloblet-set!`: `x3` into field `x2` (8k) of the
                    // bloblet in `x1`, 2 ≤ k ≤ F, its fields not frozen, as
                    // register code's `field!` does (`TODO.md` §57); else the
                    // call-out, which refuses it or reports it.
                    if let Callout::Prim { p, n: 3 } = c
                        && fixpt_runtime::PRIMITIVES[p].name == "%bloblet-set!"
                    {
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
                        // The header: F + 1 words before the suffix.
                        a.e(sub(X11, 1, X16));
                        a.e(ldur(X13, X11, -12));
                        a.e(ubfx(X13, X13, fixpt_heap::layout::H_FIELDS_FROZEN.lo, 1));
                        a.e(cmp_imm(X13, 0));
                        a.to(slow, Fix::If(Cond::Ne));
                        a.e(sub(X11, 1, 2));
                        a.e(stur(3, X11, -4));
                        a.es(&card_mark(X11, -4, ST, st_off(offset_of!(DState, cards)), X13, X16));
                        a.es(&mov_imm64(RESULT, Value::UNSPECIFIED.raw()));
                        a.to(done, Fix::B);
                    }
                    // A native closure over REG1…REGn likewise, from the free
                    // space: its header; its free values, the code, and the
                    // trailer, fields counted back from where it points.
                    if let (Callout::Closure { n }, Some(f)) = (c, code_field)
                        && n <= 8
                    {
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
                    if raw_store && matches!(c, Callout::Prim { p, n: 3 } if fixpt_runtime::PRIMITIVES[p].name == "%fx26-flatarray-set!") {
                        box_f64(&mut a, self.callouts, 3);
                    }
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
                        for j in 0..c.arity().min(8) {
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
                    // A global bound as compiled: while its cell has not
                    // been written since, as bound; else, out of the way,
                    // through the cell, as what it holds now.
                    if let Some((cell, writes)) = bound.take() {
                        let (slow, join) = (a.label(), a.label());
                        let fc = self.field(p, Field::Cell(cell));
                        ldr_field(&mut a, X9, fc);
                        a.e(ldur(CLO, X9, field_off(2)));
                        a.e(ldur(X11, X9, field_off(GLOBAL_WRITES)));
                        a.es(&mov_imm64(X16, writes.raw()));
                        a.e(cmp(X11, X16));
                        a.to(slow, Fix::If(Cond::Ne));
                        match pending.take() {
                            Some(Field::Code(q)) => {
                                let f = self.field(p, Field::Code(q));
                                ldr_field(&mut a, X16, f);
                            }
                            Some(g) => {
                                let f = self.field(p, g);
                                ldr_field(&mut a, CLO, f);
                                a.e(ldur(X16, CLO, field_off(CLOSURE_WORD)));
                            }
                            None => unreachable!("a global bound is called"),
                        }
                        a.bind(join);
                        cell_slows.push((slow, join, stub));
                        foreign.push((stub, after, k(o(0)), tail));
                    } else {
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
                    }
                    // The count, for a variadic callee (`vargs`), Larceny's
                    // way: every call passes it.
                    a.e(movz(X9, k(o(0)) as u32, 0));
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
                    let l = edge(&mut a, si - 1, to);
                    if op != "branch" {
                        a.es(&mov_imm64(X16, Value::FALSE.raw()));
                        a.e(cmp(RESULT, X16));
                        a.to(l, Fix::If(if op == "branchf" { Cond::Eq } else { Cond::Ne }));
                    } else {
                        if back_to[to] {
                            a.e(subs_imm(FUEL, FUEL, 1));
                            trap(&mut a, &mut stubs, OUT_OF_FUEL, Cond::Lo);
                        }
                        a.to(l, Fix::B);
                    }
                }
                other => return decline(format!("`{other}`")),
            }
        }
        a.bind(labels[cells.len()]);
        }
        // The ints' slow paths.
        for slow in int_slows {
            slow.emit(&mut a, self.callouts, &mut stubs);
        }
        // The ways in that unbox first, or test for fixnums (going over to
        // the general version where one is not).
        for (l, unbox, check, to, general) in edge_stubs {
            a.bind(l);
            for (r, rep) in unbox {
                unbox_to(&mut a, self.callouts, r as Reg, rep);
            }
            for r in check {
                check_fixnum(&mut a, r as Reg, general);
            }
            a.to(to, Fix::B);
        }
        let own = a.code.len();
        // The calls of what is not native code, out of the way: the common
        // routine, in a frame of its own with nothing in it, calls out with
        // the arguments and the callee, and returns its value; a tail call
        // goes there to return from it to this procedure's caller.
        // Each call of what is not native code: to the machine's common
        // routine (`common_foreign`), with the arguments' count.
        for (slow, join, stub) in &cell_slows {
            a.bind(*slow);
            a.e(ldur(X16, CLO, field_off(CLOSURE_WORD)));
            a.e(ldr(X17, ST, st_off(offset_of!(DState, code_lo))));
            a.e(cmp(X16, X17));
            a.to(*stub, Fix::If(Cond::Lo));
            a.to(*join, Fix::B);
        }
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
        let info = overflow_info(self.procs[p].arity, captures);
        for (over, back) in &overflows {
            a.bind(*over);
            // Through the link, which the frame holds already: X9 may be a
            // variadic procedure's count.
            ldr_field(&mut a, X16, 1);
            a.es(&mov_imm64(X17, info));
            a.e(ldr(LINK, ST, st_off(offset_of!(DState, overflow))));
            a.e(blr(LINK));
            a.to(*back, Fix::B);
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

/// The slow path of an `int` operation (`op2`): a bignum operand, or a
/// sum past a fixnum, given to the runtime (`int_op`), with no collection.
struct IntSlow {
    /// Where an operand is no fixnum; where the sum overflowed, in `into`,
    /// if it is a sum or difference; where to go on.
    entry: Label,
    overflow: Option<Label>,
    back: Label,
    /// The operands (the second a register, or a small constant), where the
    /// value goes, the primitive, and whether it subtracts.
    x: Reg,
    y: Reg,
    imm: Option<u32>,
    into: Reg,
    prim: usize,
    sub: bool,
    /// A comparison a branch reads: where it goes, and whether when true.
    branch: Option<(Label, bool)>,
}

impl IntSlow {
    fn emit(&self, a: &mut Asm, callouts: &mut Vec<Callout>, stubs: &mut Vec<(Label, u32)>) {
        // A sum written over its operand: the operand again, the wrapped
        // sum undone.
        if let Some(ov) = self.overflow {
            a.bind(ov);
            if self.into == self.x {
                match (self.imm, self.sub) {
                    (Some(n), false) => a.e(sub_imm(self.x, self.into, n)),
                    (Some(n), true) => a.e(add_imm(self.x, self.into, n)),
                    (None, false) => a.e(sub(self.x, self.into, self.y)),
                    (None, true) => a.e(add(self.x, self.into, self.y)),
                }
            }
        }
        a.bind(self.entry);
        let y = match self.imm {
            Some(n) => {
                a.e(movz(X16, n, 0));
                X16
            }
            None => self.y,
        };
        pure_call(a, callouts, Callout::Pure { p: self.prim, n: 2 }, &[self.x, y], self.into);
        a.e(ldr(X9, ST, st_off(offset_of!(DState, trap))));
        a.e(cmp_imm(X9, 0));
        trap_at(a, stubs, PRIM_FAILED, Cond::Ne);
        if let Some((l, when_true)) = self.branch {
            a.es(&mov_imm64(X16, Value::TRUE.raw()));
            a.e(cmp(RESULT, X16));
            a.to(l, Fix::If(if when_true { Cond::Eq } else { Cond::Ne }));
        }
        a.to(self.back, Fix::B);
    }
}

/// A trap of kind `code` where `c` holds, by a stub of its own.
fn trap_at(a: &mut Asm, stubs: &mut Vec<(Label, u32)>, code: u32, c: Cond) {
    let l = a.label();
    stubs.push((l, code));
    a.to(l, Fix::If(c));
}

/// Call-out `c`, which never collects, on `args` (registers, put in the
/// state), its value into `into`: `RESULT`, REG1…REG8, the closure and the
/// link kept in the state around it, as they are (raw or not: nothing
/// moves), and put back.
fn pure_call(a: &mut Asm, callouts: &mut Vec<Callout>, c: Callout, args: &[Reg], into: Reg) {
    let n = callouts.len();
    callouts.push(c);
    let base = offset_of!(DState, args) as u32;
    for (j, &r) in args.iter().enumerate() {
        a.e(str(r, ST, base + 8 * j as u32));
    }
    let pairs = [(1, 2), (3, 4), (5, 6), (7, 8), (CLO, LINK), (RESULT, XZR)];
    let kept = offset_of!(DState, kept) as u32;
    a.e(add_imm(X16, ST, kept));
    for (j, &(r1, r2)) in pairs.iter().enumerate() {
        a.e(stp(r1, r2, X16, 16 * j as i64));
    }
    call_out(a, n);
    a.e(mov(X17, RESULT));
    a.e(add_imm(X16, ST, kept));
    for (j, &(r1, r2)) in pairs.iter().enumerate() {
        a.e(ldp(r1, r2, X16, 16 * j as i64));
    }
    if into != X17 {
        a.e(mov(into, X17));
    }
}

/// Register `r`'s raw `i64` (signed) or `u64` boxed, in place: a fixnum
/// where it fits, else a bignum, made by a call-out.
fn box_reg(a: &mut Asm, callouts: &mut Vec<Callout>, r: Reg, signed: bool) {
    let (slow, done) = (a.label(), a.label());
    if signed {
        a.e(lsl_imm(X16, r, 3));
        a.e(asr_imm(X13, X16, 3));
        a.e(cmp(X13, r));
        a.to(slow, Fix::If(Cond::Ne));
        a.e(mov(r, X16));
    } else {
        a.e(lsr_imm(X13, r, 60));
        a.e(cmp_imm(X13, 0));
        a.to(slow, Fix::If(Cond::Ne));
        a.e(lsl_imm(r, r, 3));
    }
    a.to(done, Fix::B);
    a.bind(slow);
    pure_call(a, callouts, Callout::Box { signed }, &[r], r);
    a.bind(done);
}

/// Register `r`'s exact integer unboxed, in place: its low 64 bits, a
/// fixnum's by a shift, a bignum's by a call-out.
fn unbox_reg(a: &mut Asm, callouts: &mut Vec<Callout>, r: Reg) {
    let (slow, done) = (a.label(), a.label());
    a.e(tst_low(r, 3));
    a.to(slow, Fix::If(Cond::Ne));
    a.e(asr_imm(r, r, 3));
    a.to(done, Fix::B);
    a.bind(slow);
    pure_call(a, callouts, Callout::Unbox, &[r], r);
    a.bind(done);
}

/// The conversions `reps` asks for before an instruction; a test for a
/// fixnum going to `general` (the instruction in the general version) where
/// it fails.
/// `result` is where `RESULT`'s value is (`src`).
fn convert(a: &mut Asm, callouts: &mut Vec<Callout>, cs: &[Convert], general: Label, result: Reg) {
    for c in cs {
        match *c {
            Convert::Box { r, rep: Rep::Raw { signed } } => box_reg(a, callouts, r as Reg, signed),
            Convert::Box { r, .. } => box_f64(a, callouts, r as Reg),
            Convert::Unbox { r, rep } => unbox_to(a, callouts, r as Reg, rep),
            Convert::Check { r } => check_fixnum(a, if r == 0 { result } else { r as Reg }, general),
        }
    }
}

/// Register `r` tested for a fixnum, to `general` if it is not one.
fn check_fixnum(a: &mut Asm, r: Reg, general: Label) {
    a.e(tst_low(r, 3));
    a.to(general, Fix::If(Cond::Ne));
}

/// Register `r`'s value unboxed to `rep`.
fn unbox_to(a: &mut Asm, callouts: &mut Vec<Callout>, r: Reg, rep: Rep) {
    match rep {
        Rep::F64 => unbox_f64(a, r),
        _ => unbox_reg(a, callouts, r),
    }
}

/// Register `r`'s flonum unboxed, in place: its double's bits, the word its
/// pointer is 4 past. Anything but a bloblet (a register dead where ways
/// meet may hold anything) gives 0, and is not read.
fn unbox_f64(a: &mut Asm, r: Reg) {
    let (other, done) = (a.label(), a.label());
    a.e(and_low(X16, r, 3));
    a.e(cmp_imm(X16, fixpt_heap::value::TAG_BLOBLET as u32));
    a.to(other, Fix::If(Cond::Ne));
    a.e(ldur(r, r, -4));
    a.to(done, Fix::B);
    a.bind(other);
    a.e(movz(r, 0, 0));
    a.bind(done);
}

/// Register `r`'s raw `f64` boxed, in place: a flonum from the free space
/// when there is room short of the collection's threshold (a header and the
/// bits, as `Heap::make_flonum` makes it), else by a call-out that does not
/// collect. Uses X11 and X13 to X17.
fn box_f64(a: &mut Asm, callouts: &mut Vec<Callout>, r: Reg) {
    let (slow, done) = (a.label(), a.label());
    a.e(ldr(X13, ST, st_off(offset_of!(DState, top))));
    a.e(ldr(X14, X13, 0));
    a.e(ldr(X15, ST, st_off(offset_of!(DState, alloc_limit))));
    a.e(add_imm(X16, X14, 2));
    a.e(cmp(X16, X15));
    a.to(slow, Fix::If(Cond::Hi));
    a.e(ldr(X17, ST, st_off(offset_of!(DState, words))));
    a.e(add_lsl(X11, X17, X14, 3));
    let header = fixpt_heap::value::make_header(fixpt_heap::ObjType::Flonum as u8, 0, 8);
    a.es(&mov_imm64(X17, header));
    a.e(str(X17, X11, 0));
    a.e(str(r, X11, 8));
    a.e(str(X16, X13, 0));
    a.e(add_imm(r, X11, 8 + fixpt_heap::value::TAG_BLOBLET as u32));
    a.to(done, Fix::B);
    a.bind(slow);
    pure_call(a, callouts, Callout::BoxF64, &[r], r);
    a.bind(done);
}

/// `int->f64` (primitive `p`) of the int in `RESULT`, raw into `RESULT`: a
/// fixnum's by `scvtf`, correctly rounded; a bignum's by the primitive.
fn f64_of_int(a: &mut Asm, callouts: &mut Vec<Callout>, p: usize) {
    let (slow, done) = (a.label(), a.label());
    a.e(tst_low(RESULT, 3));
    a.to(slow, Fix::If(Cond::Ne));
    a.e(asr_imm(X13, RESULT, 3));
    a.e(scvtf(16, X13));
    a.e(fmov_from_d(RESULT, 16));
    a.to(done, Fix::B);
    a.bind(slow);
    pure_call(a, callouts, Callout::Pure { p, n: 1 }, &[RESULT], RESULT);
    unbox_f64(a, RESULT);
    a.bind(done);
}

/// `f64->int` (primitive `p`) of the raw `f64` in `RESULT`, into `RESULT`:
/// by `fcvtzs` where that is exact and a fixnum; else the primitive's, on the
/// boxed value (a bignum, or its failure: not an integer).
fn int_of_f64(a: &mut Asm, callouts: &mut Vec<Callout>, stubs: &mut Vec<(Label, u32)>, p: usize) {
    let (slow, done) = (a.label(), a.label());
    a.e(fmov_to_d(16, RESULT));
    a.e(fcvtzs(X13, 16));
    a.e(scvtf(17, X13));
    a.e(fcmp(16, 17));
    a.to(slow, Fix::If(Cond::Ne));
    a.e(lsl_imm(X14, X13, 3));
    a.e(asr_imm(X15, X14, 3));
    a.e(cmp(X15, X13));
    a.to(slow, Fix::If(Cond::Ne));
    a.e(mov(RESULT, X14));
    a.to(done, Fix::B);
    a.bind(slow);
    box_f64(a, callouts, RESULT);
    pure_call(a, callouts, Callout::Pure { p, n: 1 }, &[RESULT], RESULT);
    a.e(ldr(X9, ST, st_off(offset_of!(DState, trap))));
    a.e(cmp_imm(X9, 0));
    trap_at(a, stubs, PRIM_FAILED, Cond::Ne);
    a.bind(done);
}

/// `out` := how many elements the flat array in `arr` has (untagged): its
/// suffix's bytes, from its header 28 bytes before its pointer (a flat
/// array has one field and a trailer), over its elements' size, from its
/// layout in field 2. Uses X11 and X16 (not X17, where a constant operand
/// may be).
fn flat_count(a: &mut Asm, arr: Reg, out: Reg) {
    use fixpt_heap::layout::*;
    a.e(ldur(out, arr, -28));
    a.e(lsr_imm(out, out, 32));
    a.e(ldur(X16, arr, field_off(2)));
    a.e(lsr_imm(X16, X16, 3));
    // The 8-byte layouts, as bits of a word: 2 plus that bit is the shift.
    let wide = [FLAT_I64, FLAT_U64, FLAT_F64].iter().fold(0u32, |m, c| m | 1 << c);
    a.e(movz(X11, wide, 0));
    a.e(lsrv(X11, X11, X16));
    a.e(and_low(X11, X11, 1));
    a.e(add_imm(X11, X11, 2));
    a.e(lsrv(out, out, X11));
}

/// Where a flat array's elements are, and element `index` (in `y`, a
/// value): X14 the index, X15 the suffix, X16 the layout, as a fixnum; to
/// `slow` unless the index is a fixnum in range.
fn flat_element(a: &mut Asm, arr: Reg, y: Reg, slow: Label) {
    a.e(tst_low(y, 3));
    a.to(slow, Fix::If(Cond::Ne));
    a.e(asr_imm(X14, y, 3));
    flat_count(a, arr, X13);
    a.e(cmp(X14, X13));
    a.to(slow, Fix::If(Cond::Hs));
    a.e(ldur(X16, arr, field_off(2)));
    a.e(sub_imm(X15, arr, fixpt_heap::value::TAG_BLOBLET as u32));
}

/// `flatarray-ref` of the flat array in `RESULT` at `y`, into `RESULT`, by
/// its layout: an `f64` boxed from the free space (`slow`, the primitive's,
/// when there is no room), an `f32` an immediate, a 32-bit integer its
/// fixnum, a 64-bit one its fixnum where it is one (else `slow`).
fn flat_ref(a: &mut Asm, y: Reg, slow: Label) {
    use fixpt_heap::layout::*;
    let end = a.label();
    flat_element(a, RESULT, y, slow);
    let is = |a: &mut Asm, code: i64, not: Label| {
        a.e(cmp_imm(X16, (code << 3) as u32));
        a.to(not, Fix::If(Cond::Ne));
    };
    let (not_f64, not_f32, not_i32, not_u32) = (a.label(), a.label(), a.label(), a.label());
    is(a, FLAT_F64, not_f64);
    a.e(ldr_x8(X9, X15, X14));
    a.e(ldr(X13, ST, st_off(offset_of!(DState, top))));
    a.e(ldr(X14, X13, 0));
    a.e(ldr(X15, ST, st_off(offset_of!(DState, alloc_limit))));
    a.e(add_imm(X16, X14, 2));
    a.e(cmp(X16, X15));
    a.to(slow, Fix::If(Cond::Hi));
    a.e(ldr(X17, ST, st_off(offset_of!(DState, words))));
    a.e(add_lsl(X11, X17, X14, 3));
    a.es(&mov_imm64(X17, fixpt_heap::value::make_header(fixpt_heap::ObjType::Flonum as u8, 0, 8)));
    a.e(str(X17, X11, 0));
    a.e(str(X9, X11, 8));
    a.e(str(X16, X13, 0));
    a.e(add_imm(RESULT, X11, 8 + fixpt_heap::value::TAG_BLOBLET as u32));
    a.to(end, Fix::B);
    a.bind(not_f64);
    is(a, FLAT_F32, not_f32);
    a.e(ldr_w4(X13, X15, X14));
    a.e(lsl_imm(X13, X13, 32));
    a.e(add_imm(RESULT, X13, (Value::f32(0.0).raw() & 0xff) as u32));
    a.to(end, Fix::B);
    a.bind(not_f32);
    is(a, FLAT_I32, not_i32);
    a.e(ldrsw_4(X13, X15, X14));
    a.e(lsl_imm(RESULT, X13, 3));
    a.to(end, Fix::B);
    a.bind(not_i32);
    is(a, FLAT_U32, not_u32);
    a.e(ldr_w4(X13, X15, X14));
    a.e(lsl_imm(RESULT, X13, 3));
    a.to(end, Fix::B);
    // `i64` or `u64`: a fixnum where it fits one.
    a.bind(not_u32);
    a.e(ldr_x8(X13, X15, X14));
    let unsigned = a.label();
    a.e(cmp_imm(X16, (FLAT_U64 << 3) as u32));
    a.to(unsigned, Fix::If(Cond::Eq));
    a.e(lsl_imm(X14, X13, 3));
    a.e(asr_imm(X15, X14, 3));
    a.e(cmp(X15, X13));
    a.to(slow, Fix::If(Cond::Ne));
    a.e(mov(RESULT, X14));
    a.to(end, Fix::B);
    a.bind(unsigned);
    a.e(lsr_imm(X15, X13, 60));
    a.e(cmp_imm(X15, 0));
    a.to(slow, Fix::If(Cond::Ne));
    a.e(lsl_imm(RESULT, X13, 3));
    a.bind(end);
}

/// `flatarray-set!` of the flat array in `x1` at `x2` to `x3`, as its
/// layout keeps it: to `slow` (the call-out) for an index out of range, or
/// a 64-bit integer that is a bignum; else unit into `RESULT`, and to `done`.
/// `raw`: the value is an `f64`'s bits, so the array's elements are `f64`s.
fn flat_set(a: &mut Asm, slow: Label, done: Label, raw: bool) {
    use fixpt_heap::layout::*;
    let (v, stored) = (3 as Reg, a.label());
    flat_element(a, 1, 2, slow);
    let is = |a: &mut Asm, code: i64, not: Label| {
        a.e(cmp_imm(X16, (code << 3) as u32));
        a.to(not, Fix::If(Cond::Ne));
    };
    if raw {
        a.e(str_x8(v, X15, X14));
        a.es(&mov_imm64(RESULT, Value::UNIT.raw()));
        a.to(done, Fix::B);
        return;
    }
    let (not_f64, not_f32, wide) = (a.label(), a.label(), a.label());
    is(a, FLAT_F64, not_f64);
    a.e(ldur(X13, v, -(fixpt_heap::value::TAG_BLOBLET as i64)));
    a.e(str_x8(X13, X15, X14));
    a.to(stored, Fix::B);
    a.bind(not_f64);
    is(a, FLAT_F32, not_f32);
    a.e(lsr_imm(X13, v, 32));
    a.e(str_w4(X13, X15, X14));
    a.to(stored, Fix::B);
    // A 32-bit integer is the fixnum of its value; a 64-bit one may be a
    // bignum, the call-out's.
    a.bind(not_f32);
    a.e(cmp_imm(X16, (FLAT_I64 << 3) as u32));
    a.to(wide, Fix::If(Cond::Eq));
    a.e(cmp_imm(X16, (FLAT_U64 << 3) as u32));
    a.to(wide, Fix::If(Cond::Eq));
    a.e(asr_imm(X13, v, 3));
    a.e(str_w4(X13, X15, X14));
    a.to(stored, Fix::B);
    a.bind(wide);
    a.e(tst_low(v, 3));
    a.to(slow, Fix::If(Cond::Ne));
    a.e(asr_imm(X13, v, 3));
    a.e(str_x8(X13, X15, X14));
    a.bind(stored);
    a.es(&mov_imm64(RESULT, Value::UNIT.raw()));
    a.to(done, Fix::B);
}

/// An `f32` operation `what` (the name after `f32`) on the immediates in
/// `RESULT` and `y`, into `RESULT`: each unboxed by a shift into `s16` and
/// `s17`, the result boxed by a shift and the subtag's add. False for one
/// the runtime does (`min`, `max`, conversions): nothing is emitted.
fn f32_fast(a: &mut Asm, what: &str, y: Reg) -> bool {
    let test = match what {
        "<" => Some(Cond::Mi),
        "<=" => Some(Cond::Ls),
        ">" => Some(Cond::Gt),
        ">=" => Some(Cond::Ge),
        "=" => Some(Cond::Eq),
        _ => None,
    };
    let op = match what {
        "+" => Some(fadd(16, 16, 17)),
        "-" => Some(fsub(16, 16, 17)),
        "*" => Some(fmul(16, 16, 17)),
        "/" => Some(fdiv(16, 16, 17)),
        "-abs" => Some(fabs(16, 16)),
        "-neg" => Some(fneg(16, 16)),
        "-sqrt" => Some(fsqrt(16, 16)),
        "-floor" => Some(frintm(16, 16)),
        "-ceiling" => Some(frintp(16, 16)),
        "-truncate" => Some(frintz(16, 16)),
        "-round" => Some(frintn(16, 16)),
        _ => None,
    };
    if test.is_none() && op.is_none() {
        return false;
    }
    a.e(lsr_imm(X13, RESULT, 32));
    a.e(fmov_to_s(16, X13));
    a.e(lsr_imm(X14, y, 32));
    a.e(fmov_to_s(17, X14));
    if let Some(c) = test {
        a.e(single(fcmp(16, 17)));
        a.es(&mov_imm64(X13, Value::TRUE.raw()));
        a.es(&mov_imm64(X14, Value::FALSE.raw()));
        a.e(csel(RESULT, X13, X14, c));
        return true;
    }
    a.e(single(op.expect("an operation")));
    a.e(fmov_from_s(X13, 16));
    a.e(lsl_imm(X13, X13, 32));
    a.e(add_imm(RESULT, X13, (Value::f32(0.0).raw() & 0xff) as u32));
    true
}

/// An `f64` operation `what` (as `reps::raw_op` names it), on raw `RESULT`
/// and `y`, into `RESULT`: raw, or a comparison's boolean. By way of `d16`
/// and `d17`, which nothing else keeps anything in.
fn f64_fast(a: &mut Asm, what: &str, y: Reg) {
    const D16: Reg = 16;
    const D17: Reg = 17;
    a.e(fmov_to_d(D16, RESULT));
    a.e(fmov_to_d(D17, y));
    let test = match what {
        "<" => Some(Cond::Mi),
        "<=" => Some(Cond::Ls),
        ">" => Some(Cond::Gt),
        ">=" => Some(Cond::Ge),
        "=" => Some(Cond::Eq),
        _ => None,
    };
    if let Some(c) = test {
        a.e(fcmp(D16, D17));
        a.es(&mov_imm64(X13, Value::TRUE.raw()));
        a.es(&mov_imm64(X14, Value::FALSE.raw()));
        a.e(csel(RESULT, X13, X14, c));
        return;
    }
    a.e(match what {
        "+" => fadd(D16, D16, D17),
        "-" => fsub(D16, D16, D17),
        "*" => fmul(D16, D16, D17),
        "/" => fdiv(D16, D16, D17),
        "-abs" => fabs(D16, D16),
        "-neg" => fneg(D16, D16),
        "-sqrt" => fsqrt(D16, D16),
        "-floor" => frintm(D16, D16),
        "-ceiling" => frintp(D16, D16),
        "-truncate" => frintz(D16, D16),
        _ => frintn(D16, D16),
    });
    a.e(fmov_from_d(RESULT, D16));
}

/// An `i64` (signed) or `u64` operation `what` (as `reps::raw_op` names
/// it) on raw `RESULT` and `y` (raw, or a shift's count, a fixnum), into
/// `RESULT`: raw, or a comparison's boolean (`T->int` is a boxing,
/// `box_reg`). Its arithmetic wraps, as the machine's does. Uses X13 to
/// X16.
fn raw_fast(a: &mut Asm, stubs: &mut Vec<(Label, u32)>, signed: bool, what: &str, y: Reg) {
    let x = RESULT;
    let compare = |c: Cond| match (c, signed) {
        (Cond::Lt, false) => Cond::Lo,
        (Cond::Le, false) => Cond::Ls,
        (Cond::Gt, false) => Cond::Hi,
        (Cond::Ge, false) => Cond::Hs,
        (c, _) => c,
    };
    let test = match what {
        "<" => Some(Cond::Lt),
        "<=" => Some(Cond::Le),
        ">" => Some(Cond::Gt),
        ">=" => Some(Cond::Ge),
        "=" => Some(Cond::Eq),
        _ => None,
    };
    if let Some(c) = test {
        a.e(cmp(x, y));
        a.es(&mov_imm64(X13, Value::TRUE.raw()));
        a.es(&mov_imm64(X14, Value::FALSE.raw()));
        a.e(csel(RESULT, X13, X14, compare(c)));
        return;
    }
    let nonzero = |a: &mut Asm, stubs: &mut Vec<(Label, u32)>| {
        a.e(cmp_imm(y, 0));
        trap_at(a, stubs, DIVIDED_BY_ZERO, Cond::Eq);
    };
    match what {
        // `int->T`: its operand unboxed is it, wrapped.
        "from" => {}
        "+" => a.e(add(RESULT, x, y)),
        "-" => a.e(sub(RESULT, x, y)),
        "*" => a.e(mul(RESULT, x, y)),
        "-and" => a.e(and(RESULT, x, y)),
        "-or" => a.e(orr(RESULT, x, y)),
        "-xor" => a.e(eor(RESULT, x, y)),
        "-not" => {
            a.e(sub(RESULT, XZR, x));
            a.e(sub_imm(RESULT, RESULT, 1));
        }
        "-quotient" => {
            nonzero(a, stubs);
            a.e(if signed { sdiv(RESULT, x, y) } else { udiv(RESULT, x, y) });
        }
        "-remainder" => {
            nonzero(a, stubs);
            a.e(if signed { sdiv(X13, x, y) } else { udiv(X13, x, y) });
            a.e(msub(RESULT, X13, y, x));
        }
        // The count, a fixnum, modulo 64.
        "-shl" | "-shr" => {
            a.e(ubfx(X13, y, 3, 6));
            a.e(match (what, signed) {
                ("-shl", _) => lslv(RESULT, x, X13),
                (_, true) => asrv(RESULT, x, X13),
                _ => lsrv(RESULT, x, X13),
            });
        }
        // `->int` is `box_reg`'s.
        _ => unreachable!("a 64-bit operation"),
    }
}

/// `RESULT`, the fixnum of an integer, wrapped to a 32-bit type's range: its
/// bits 3 to 34 kept, sign-extended if the type is signed.
fn wrap32(a: &mut Asm, signed: bool) {
    if signed {
        a.e(lsl_imm(RESULT, RESULT, 29));
        a.e(asr_imm(RESULT, RESULT, 29));
    } else {
        a.e(and_bits(RESULT, RESULT, 3, 32));
    }
}

/// A shape predicate's fast path (`docs/research/logical-types.md`, L1;
/// `TODO.md` §56), on `RESULT` into `RESULT`: by the value's tag, and for a
/// bloblet by its header's kind, found as the word before the suffix or as
/// far back as the trailer there says; anything else (fields and no
/// trailer, a large header) to `slow`. False if `name` is none. Uses X13
/// to X16.
fn shape_fast(a: &mut Asm, name: &str, slow: Label) -> bool {
    use fixpt_heap::layout::kind;
    use fixpt_heap::value::{TAG_BLOBLET, TAG_HEADER, TAG_PAIR, TAG_TRAILER};
    let x = RESULT;
    let flag = |a: &mut Asm, c: Cond| {
        a.es(&mov_imm64(X15, Value::TRUE.raw()));
        a.es(&mov_imm64(X16, Value::FALSE.raw()));
        a.e(csel(RESULT, X15, X16, c));
    };
    let kinds: &[u8] = match name {
        "null?" => {
            a.es(&mov_imm64(X13, Value::NULL.raw()));
            a.e(cmp(x, X13));
            flag(a, Cond::Eq);
            return true;
        }
        "pair?" => {
            a.e(and_low(X13, x, 3));
            a.e(cmp_imm(X13, TAG_PAIR as u32));
            flag(a, Cond::Eq);
            return true;
        }
        "char?" => {
            a.e(and_low(X13, x, 8));
            a.e(cmp_imm(X13, (Value::char('\0').raw() & 0xFF) as u32));
            flag(a, Cond::Eq);
            return true;
        }
        "boolean?" => {
            a.es(&mov_imm64(X15, Value::FALSE.raw()));
            a.es(&mov_imm64(X16, Value::TRUE.raw()));
            a.e(cmp(x, X15));
            a.e(csel(X13, X16, X15, Cond::Eq));
            a.e(cmp(x, X16));
            a.e(csel(RESULT, X16, X13, Cond::Eq));
            return true;
        }
        "exact-integer?" => &[kind("bignum")],
        "symbol?" => &[kind("symbol")],
        "string?" => &[kind("string")],
        "%fx26-array?" => &[kind("bloblet")],
        "%fx26-procedure?" => &[
            kind("closure"),
            kind("primitive"),
            kind("continuation"),
            kind("cellular-closure"),
            kind("native-closure"),
            kind("cellular-continuation"),
        ],
        _ => return false,
    };
    let (yes, no, have, end) = (a.label(), a.label(), a.label(), a.label());
    // A fixnum is an exact integer.
    if name == "exact-integer?" {
        a.e(tst_low(x, 3));
        a.to(yes, Fix::If(Cond::Eq));
    }
    a.e(and_low(X13, x, 3));
    a.e(cmp_imm(X13, TAG_BLOBLET as u32));
    a.to(no, Fix::If(Cond::Ne));
    a.e(ldur(X16, x, field_off(1)));
    a.e(and_low(X13, X16, 3));
    a.e(cmp_imm(X13, TAG_HEADER as u32));
    a.to(have, Fix::If(Cond::Eq));
    a.e(cmp_imm(X13, TAG_TRAILER as u32));
    a.to(slow, Fix::If(Cond::Ne));
    a.e(sub_imm(X16, X16, TAG_TRAILER as u32));
    a.e(sub(X14, x, X16));
    a.e(ldur(X16, X14, field_off(1)));
    a.bind(have);
    let k = fixpt_heap::layout::H_KIND;
    a.e(ubfx(X13, X16, k.lo, k.width));
    a.e(cmp_imm(X13, fixpt_heap::layout::KIND_EXTENSION as u32));
    a.to(slow, Fix::If(Cond::Eq));
    for &c in kinds {
        a.e(cmp_imm(X13, c as u32));
        a.to(yes, Fix::If(Cond::Eq));
    }
    a.bind(no);
    a.es(&mov_imm64(RESULT, Value::FALSE.raw()));
    a.to(end, Fix::B);
    a.bind(yes);
    a.es(&mov_imm64(RESULT, Value::TRUE.raw()));
    a.bind(end);
    true
}

/// The fast path of primitive `name`, one that never collects and no
/// operation of `i64` or `u64` (those are `raw_fast`'s), on `RESULT` and
/// `y`, into `RESULT`, going to `slow` for what it leaves to the primitive
/// (a bignum, a zero divisor, a result past a fixnum): false if it has
/// none. An `i32` or `u32` is the fixnum of its value, so its arithmetic is
/// the fixnums' then wrapped. Uses X13 to X16.
fn pure_fast(a: &mut Asm, name: &str, y: Reg, slow: Label) -> bool {
    let x = RESULT;
    if shape_fast(a, name, slow) {
        return true;
    }
    let fixnum = |a: &mut Asm, r: Reg| {
        a.e(tst_low(r, 3));
        a.to(slow, Fix::If(Cond::Ne));
    };
    let fixnums = |a: &mut Asm| {
        a.e(orr(X13, x, y));
        a.e(tst_low(X13, 3));
        a.to(slow, Fix::If(Cond::Ne));
    };
    let nonzero = |a: &mut Asm| {
        a.e(cmp_imm(y, 0));
        a.to(slow, Fix::If(Cond::Eq));
    };
    // A product in 61 bits, or `slow`: the high word only the low's sign.
    if name == "%fx26-mul" {
        fixnums(a);
        a.e(asr_imm(X14, y, 3));
        a.e(mul(X13, x, X14));
        a.e(smulh(X15, x, X14));
        a.e(asr_imm(X16, X13, 63));
        a.e(cmp(X15, X16));
        a.to(slow, Fix::If(Cond::Ne));
        a.e(mov(RESULT, X13));
        return true;
    }
    // A quotient past a fixnum (the least one's by −1) is the primitive's;
    // a remainder is `modulo`'s when it has the divisor's sign, or is 0.
    if name == "%fx26-quotient" || name == "modulo" {
        fixnums(a);
        nonzero(a);
        a.e(sdiv(X13, x, y));
        if name == "%fx26-quotient" {
            a.e(lsl_imm(X14, X13, 3));
            a.e(asr_imm(X15, X14, 3));
            a.e(cmp(X15, X13));
            a.to(slow, Fix::If(Cond::Ne));
        } else {
            let signed = a.label();
            a.e(msub(X14, X13, y, x));
            a.e(cmp_imm(X14, 0));
            a.to(signed, Fix::If(Cond::Eq));
            a.e(eor(X15, X14, y));
            a.e(cmp_imm(X15, 0));
            a.to(signed, Fix::If(Cond::Ge));
            a.e(add(X14, X14, y));
            a.bind(signed);
        }
        a.e(mov(RESULT, X14));
        return true;
    }
    if name == "%fx26-flatarray-length" {
        flat_count(a, x, X13);
        a.e(lsl_imm(RESULT, X13, 3));
        return true;
    }
    if name == "%fx26-flatarray-ref" {
        flat_ref(a, y, slow);
        return true;
    }
    let Some(rest) = name.strip_prefix("%fx26-") else { return false };
    if let Some(what) = rest.strip_prefix("f32") {
        return f32_fast(a, what, y);
    }
    let signed = |t: &str| match t {
        "i32" => Some(true),
        "u32" => Some(false),
        _ => None,
    };
    if let Some(s) = rest.strip_prefix("int->").and_then(signed) {
        fixnum(a, x);
        wrap32(a, s);
        return true;
    }
    let Some(s) = rest.get(..3).and_then(signed) else { return false };
    let test = match &rest[3..] {
        "<" => Some(Cond::Lt),
        "<=" => Some(Cond::Le),
        ">" => Some(Cond::Gt),
        ">=" => Some(Cond::Ge),
        "=" => Some(Cond::Eq),
        _ => None,
    };
    if let Some(c) = test {
        a.e(cmp(x, y));
        a.es(&mov_imm64(X13, Value::TRUE.raw()));
        a.es(&mov_imm64(X14, Value::FALSE.raw()));
        a.e(csel(RESULT, X13, X14, c));
        return true;
    }
    match &rest[3..] {
        "->int" => {}
        "+" => {
            a.e(add(RESULT, x, y));
            wrap32(a, s);
        }
        "-" => {
            a.e(sub(RESULT, x, y));
            wrap32(a, s);
        }
        "*" => {
            a.e(asr_imm(X13, y, 3));
            a.e(mul(RESULT, x, X13));
            wrap32(a, s);
        }
        "-quotient" => {
            nonzero(a);
            a.e(sdiv(X13, x, y));
            a.e(lsl_imm(RESULT, X13, 3));
            wrap32(a, s);
        }
        "-remainder" => {
            nonzero(a);
            a.e(sdiv(X13, x, y));
            a.e(msub(RESULT, X13, y, x));
        }
        "-and" => a.e(and(RESULT, x, y)),
        "-or" => a.e(orr(RESULT, x, y)),
        "-xor" => a.e(eor(RESULT, x, y)),
        "-not" => {
            a.e(sub(RESULT, XZR, x));
            a.e(sub_imm(RESULT, RESULT, 8));
            wrap32(a, s);
        }
        "-shl" => {
            fixnum(a, y);
            a.e(ubfx(X13, y, 3, 5));
            a.e(lslv(RESULT, x, X13));
            wrap32(a, s);
        }
        // An arithmetic or logical shift right, the tag's bits cleared.
        "-shr" => {
            fixnum(a, y);
            a.e(ubfx(X13, y, 3, 5));
            a.e(if s { asrv(X14, x, X13) } else { lsrv(X14, x, X13) });
            a.e(and_bits(RESULT, X14, 3, 61));
        }
        _ => return false,
    }
    true
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
    // The stack and frame as the call-out left them: a collection flushes
    // the frames into the heap and restores the innermost elsewhere.
    a.e(ldr(X9, ST, st_off(offset_of!(DState, native_sp))));
    a.e(add_imm(SP, X9, 0));
    a.e(ldr(FRAME, ST, st_off(offset_of!(DState, fp))));
}

/// `t` := field `k` of the code bloblet being made, PC-relatively: field
/// `k` is `8k` bytes before the code's first instruction.
fn ldr_field(a: &mut Asm, t: Reg, k: usize) {
    let at = a.code.len() as i64;
    let d = -2 * k as i64 - at;
    if d < -(1 << 18) {
        a.too_far = true;
        a.e(0xD503_201F); // nop: refused at `finish`
    } else {
        a.e(ldr_lit(t, d));
    }
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
    let n = if let Callout::Foreign | Callout::ClosureAny | Callout::Rest = c { st.nargs as usize } else { c.arity() };
    // Past 8, the eighth is a list of the rest (Larceny's convention).
    let mut args: Vec<Value> = st.args[..n.min(8)].iter().map(|a| Value(*a)).collect();
    if n > 8 {
        let mut rest = args.pop().expect("eight");
        while args.len() < n {
            args.push(rt.heap.car(rest));
            rest = rt.heap.cdr(rest);
        }
    }
    if let Callout::Foreign = c {
        args.push(Value(st.aux));
    }
    let mut code = [Value(st.code)];
    // The frames walked only for a collection; none for a primitive that
    // never collects, whose caller's values are in registers.
    let quiet = matches!(c, Callout::Pure { .. } | Callout::Box { .. } | Callout::Unbox | Callout::BoxF64 | Callout::Underflow | Callout::Overflow);
    // A collection, Larceny's way (`docs/research/deep-recursion.md`): the
    // run's frames flushed into the heap first, so that the collector reads
    // no stack; then the innermost restored, where the code goes on.
    if !quiet && rt.heap.collection_due() {
        flush_all(&mut rt.heap, st);
        let mut cont = [Value(st.cont)];
        rt.heap.collect_due(&mut [&mut args, &mut code, &mut cont]);
        st.cont = cont[0].raw();
        match restore(&rt.heap, st, cont_pos(st)) {
            Ok((fp, _)) => (st.fp, st.native_sp) = (fp, fp),
            Err(why) => return failed(st, why),
        }
    }
    let out = match c {
        Callout::Cons => rt.heap.cons(args[0], args[1]).raw(),
        Callout::Box { signed } => {
            let bits = args[0].raw();
            fixpt_runtime::integer_value(rt, if signed { bits as i64 as i128 } else { bits as i128 }).raw()
        }
        Callout::Unbox => fixpt_runtime::low_64_bits(rt, args[0]),
        Callout::BoxF64 => rt.heap.make_flonum(f64::from_bits(args[0].raw())).raw(),
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
            rt.heap.push_root(Value(st.cont));
            // A native call from the cellular code runs below these frames.
            let runner = RUNNING.get().expect("native code is running");
            let outer = CALLED_OUT.replace(Some((runner, st.native_sp)));
            let r = fixpt_engine::cellular::call_value(rt, *f, args);
            CALLED_OUT.set(outer);
            let kept = rt.heap.root_at(at);
            st.cont = rt.heap.root_at(at + 1).raw();
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
                        // An abort the cellular code found no prompt for: to
                        // one in these frames, which `common_foreign` resumes
                        // at; or on, out of this run.
                        fixpt_runtime::NativeExit::Abort { tag, v } => {
                            if abort_to(rt, st, tag, v) {
                                st.foreign_resume = 1;
                                return 0;
                            }
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
        Callout::Abort => {
            abort_to(rt, st, args[0], args[1]);
            0
        }
        Callout::Underflow => match restore(&rt.heap, st, cont_pos(st)) {
            Ok((fp, pc)) => {
                st.stats.underflows += 1;
                (st.resume_sp, st.resume_fp, st.resume_pc) = (fp, fp, pc);
                0
            }
            Err(why) => failed(st, why),
        },
        Callout::Overflow => {
            let r = overflow(&mut rt.heap, st);
            st.words = rt.heap.words_address() as u64;
            r
        }
        Callout::Capture { whole } => {
            // `f`, moved by a collection, where the code reads it.
            st.args[0] = args[0].raw();
            let k = if whole {
                Some(capture_whole(rt, st))
            } else {
                capture_delimited(rt, st, args[1])
            };
            match k {
                Some(k) => k.raw(),
                None => failed(st, "call-with-composable-continuation: no prompt for this tag".into()),
            }
        }
        Callout::Reinstate => reinstate(rt, st, args[1], args[0]),
        Callout::Rest => rt.heap.list_from(&args).raw(),
        Callout::FirstMark => run_marks(&rt.heap, st, args[0]).first().copied().unwrap_or(args[1]).raw(),
        Callout::CurrentMarks => {
            let marks = run_marks(&rt.heap, st, args[0]);
            rt.heap.list_from(&marks).raw()
        }
        Callout::MarksOf => match marks_of(&rt.heap, args[0], args[1]) {
            Some(marks) => rt.heap.list_from(&marks).raw(),
            None => failed(st, "marks-of: not a continuation".into()),
        },
        Callout::Prim { p, .. } | Callout::Pure { p, .. } => {
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

/// An abort to `tag` with `v`: to the innermost prompt for it in this run's
/// frames, on the stack or in the stack cache's chain, whose frame is put
/// on top and resumed at its landing, with what the regions entered inside
/// it held gone (whether it was is the result); or, none here, out of this
/// run, to the machine that called it, which looks further (`ABORTED`; the
/// run traps).
fn abort_to(rt: &mut fixpt_runtime::Runtime, st: &mut DState, tag: Value, v: Value) -> bool {
    let on_stack = frames(st).find(|&(fp, end)| is_control(fp, end, PROMPT_MARK, tag)).map(|(pf, _)| pf);
    let pf = match on_stack {
        Some(pf) => Some(pf),
        // In the chain: every frame newer dropped, the prompt's restored.
        None => match records(&rt.heap, cont_pos(st)).into_iter().find(|r| r.is_control(PROMPT_MARK, tag)) {
            Some(r) => match restore(&rt.heap, st, r.pos()) {
                Ok((pf, _)) => Some(pf),
                Err(why) => {
                    failed(st, why);
                    return false;
                }
            },
            None => None,
        },
    };
    match pf {
        Some(pf) => {
            rt.heap.region_exit(Value(word(pf + 40)).as_fixnum() as usize);
            (st.resume_sp, st.resume_fp, st.resume_pc, st.resume_x0) = (pf, pf, word(pf + 8), v.raw());
            true
        }
        None => {
            ABORTED.with(|a| a.set(Some((tag, v))));
            failed(st, "abort: no prompt for this tag".into());
            false
        }
    }
}

/// A call-out's failure, saying why: the call traps.
fn failed(st: &mut DState, why: String) -> u64 {
    LAST_MESSAGE.with(|c| *c.borrow_mut() = Some(why));
    st.trap = PRIM_FAILED as u64;
    0
}

/// The word at `at`, on the native stack.
fn word(at: u64) -> u64 {
    // SAFETY: a word of the native stack, above its limit, which no Rust
    // code holds while the call-out runs.
    unsafe { *(at as *const u64) }
}

fn set_word(at: u64, w: u64) {
    // SAFETY: a word of the native stack, above its limit, which no Rust
    // code holds while the call-out runs.
    unsafe { *(at as *mut u64) = w }
}

/// Each native frame on the stack, innermost first, from the one that
/// called out: where it starts, and where it ends (its caller's frame, or
/// the stack's top). The run's older frames may be in the stack cache's
/// chain (`st.cont`).
fn frames_of(st: &DState) -> Vec<(u64, u64)> {
    frames(st).collect()
}

/// The same, one at a time, so that a search stops where it finds.
fn frames(st: &DState) -> impl Iterator<Item = (u64, u64)> + use<> {
    frames_from(st.fp, st.stack_top)
}

/// The frames from the one at `fp` (a native frame of the run whose top is
/// `top`) on.
fn frames_from(mut fp: u64, top: u64) -> impl Iterator<Item = (u64, u64)> {
    std::iter::from_fn(move || {
        if fp == 0 || fp >= top {
            return None;
        }
        let at = fp;
        let caller = word(at);
        let end = if caller > at && caller <= top { caller } else { top };
        fp = if end == caller { caller } else { 0 };
        Some((at, end))
    })
}

/// Whether the frame at `fp` is a control frame of `marker` for `key`.
fn is_control(fp: u64, end: u64, marker: Value, key: Value) -> bool {
    end - fp == CONTROL_FRAME && word(fp + 16) == marker.raw() && word(fp + 24) == key.raw()
}

/// A place in the stack cache's chain: a chunk, where in it a frame starts,
/// and where that frame resumes; or the chain's end (`#f`). And, once
/// looked up, where the chunk's words are and how many: nothing collects
/// while a place is walked, so they stay where they are.
#[derive(Clone, Copy)]
struct Pos {
    chunk: Value,
    at: usize,
    pc: u64,
    words: *const u64,
    len: usize,
}

const END: Pos = Pos::new(Value::FALSE, 0, 0);

impl Pos {
    const fn new(chunk: Value, at: usize, pc: u64) -> Pos {
        Pos { chunk, at, pc, words: std::ptr::null(), len: 0 }
    }
}

/// The rest of this run's frames, in the heap.
fn cont_pos(st: &DState) -> Pos {
    Pos::new(Value(st.cont), st.cont_at as usize, st.cont_pc)
}

fn set_cont(st: &mut DState, p: Pos) {
    (st.cont, st.cont_at, st.cont_pc) = (p.chunk.raw(), p.at as u64, p.pc);
}

/// A frame of the chain: its chunk, where in it it starts, its words, its
/// second word, where it resumes, and where its chunk's words are.
#[derive(Clone, Copy)]
struct Rec {
    chunk: Value,
    at: usize,
    n: usize,
    w8: u64,
    pc: u64,
    words: *const u64,
}

impl Rec {
    /// Its `j`th word from the third on.
    fn word(&self, j: usize) -> Value {
        // SAFETY: within its chunk (`j < n - 2`), which does not move
        // while the chain is walked.
        Value(unsafe { *self.words.add(self.at + 2 + j) })
    }
    /// Whether it is left by a return to its second word (a procedure's
    /// frame, a stub's, a mark's in tail position), not popped by the code
    /// of the frame it is in (a prompt's, a mark's).
    fn returns(&self) -> bool {
        if self.n != CONTROL_FRAME as usize / 8 {
            return true;
        }
        let m = self.word(0);
        !(m == PROMPT_MARK || (m == MARK_MARK && self.w8 == 0))
    }
    fn is_control(&self, marker: Value, key: Value) -> bool {
        self.n == CONTROL_FRAME as usize / 8 && self.word(0) == marker && self.word(1) == key
    }
    fn is_tail_mark(&self) -> bool {
        self.n == CONTROL_FRAME as usize / 8 && self.word(0) == MARK_MARK && self.w8 != 0
    }
    fn pos(&self) -> Pos {
        Pos::new(self.chunk, self.at, self.pc)
    }
}

/// The frame at `p`, and the place after it; none at the chain's end.
fn step(heap: &Heap, p: Pos) -> Option<(Rec, Pos)> {
    let (mut chunk, mut at, mut words, mut len) = (p.chunk, p.at, p.words, p.len);
    if chunk == Value::FALSE {
        return None;
    }
    if words.is_null() {
        let w = heap.obj_words(chunk);
        (words, len) = (w.as_ptr(), w.len());
    }
    while at >= len {
        // SAFETY: the chunk's header words, which do not move while the
        // chain is walked.
        let (next, next_at) = unsafe { (Value(*words.add(CH_NEXT)), Value(*words.add(CH_NEXT_AT)).as_fixnum() as usize) };
        if next == Value::FALSE {
            return None;
        }
        let w = heap.obj_words(next);
        (chunk, at, words, len) = (next, next_at, w.as_ptr(), w.len());
    }
    // SAFETY: a frame's first two words, within its chunk.
    let (n, w8) = unsafe { (Value(*words.add(at)).as_fixnum() as usize, Value(*words.add(at + 1)).as_fixnum() as u64) };
    Some((Rec { chunk, at, n, w8, pc: p.pc, words }, Pos { chunk, at: at + n, pc: w8, words, len }))
}

/// Each frame of the chain from `p`, newest first.
fn records(heap: &Heap, mut p: Pos) -> Vec<Rec> {
    let mut out = Vec::new();
    while let Some((r, q)) = step(heap, p) {
        out.push(r);
        p = q;
    }
    out
}

/// How many words of frames the chain from `p` holds.
fn chain_words(heap: &Heap, p: Pos) -> u64 {
    if p.chunk == Value::FALSE {
        return 0;
    }
    (heap.obj_len(p.chunk) - p.at.min(heap.obj_len(p.chunk))) as u64 + heap.obj_ref(p.chunk, CH_REST).as_fixnum() as u64
}

/// The stack map of the frame from `fp` to `end`: the mask of the words
/// from its third on that are values to keep (the third itself, the map or
/// a control frame's marker, always; all of a control frame, and of one
/// too wide for a map). What it leaves out, dead or not a value, a chunk
/// keeps as the fixnum 0.
fn kept_mask(fp: u64, end: u64) -> u64 {
    if end - fp <= 16 {
        return 0;
    }
    let head = Value(word(fp + 16));
    if !head.is_fixnum() || head.as_fixnum() < 0 { u64::MAX } else { (head.as_fixnum() as u64) << 1 | 1 }
}

/// The stack's `frames`, innermost first, copied into the heap onto the
/// chain at `tail` (older than they), in chunks of about `CHUNK_WORDS`:
/// each frame as it was, its link its size, its dead words 0; the
/// outermost's second word `last` (where the chain at `tail` resumes, if
/// that frame's own says the underflow). Where the innermost is, its `pc`
/// for the caller to say. Allocates and never collects, so what the frames
/// and `tail` hold stays where it is.
fn chunks_of(heap: &mut Heap, frames: &[(u64, u64)], last: u64, tail: Pos) -> Pos {
    let (mut next, mut rest) = ((tail.chunk, tail.at), chain_words(heap, tail));
    let mut i = frames.len();
    while i > 0 {
        let (mut j, mut w) = (i, 0);
        while j > 0 {
            let (fp, end) = frames[j - 1];
            let fw = ((end - fp) / 8) as usize;
            if w > 0 && w + fw > CHUNK_WORDS {
                break;
            }
            w += fw;
            j -= 1;
        }
        // Frames `j..i`, a word at a time: which frame, and where in it.
        let (mut f, mut k, mut mask) = (j, 0usize, kept_mask(frames[j].0, frames[j].1));
        let outermost = frames.len() - 1;
        let chunk = heap.vector_with(CH_FRAMES + w, |at| match at {
            CH_NEXT => next.0,
            CH_NEXT_AT => Value::fixnum(next.1 as i64),
            CH_REST => Value::fixnum(rest as i64),
            _ => {
                let (fp, end) = frames[f];
                let v = match k {
                    0 => Value::fixnum(((end - fp) / 8) as i64),
                    1 => Value::fixnum(if f == outermost { last } else { word(fp + 8) } as i64),
                    _ => {
                        let j = k - 2;
                        if j >= 64 || mask & (1 << j) != 0 { Value(word(fp + 8 * k as u64)) } else { Value::fixnum(0) }
                    }
                };
                k += 1;
                if fp + 8 * k as u64 == end && f + 1 < i {
                    f += 1;
                    k = 0;
                    mask = kept_mask(frames[f].0, frames[f].1);
                }
                v
            }
        });
        next = (chunk, CH_FRAMES);
        rest += w as u64;
        i = j;
    }
    Pos::new(next.0, next.1, 0)
}

/// The second word the outermost of this run's frames on the stack should
/// have in the chain: where the chain resumes, if there is one (the frame's
/// own says the underflow), else its own (the bottom's).
fn outermost_second(st: &DState, outermost: u64) -> u64 {
    if step_nonempty(st) { st.cont_pc } else { word(outermost + 8) }
}

fn step_nonempty(st: &DState) -> bool {
    st.cont != Value::FALSE.raw()
}

/// Frames restored from the chain at `p` onto the run's empty stack cache,
/// at its top: at least one, and on to `RESTORE_WORDS`, never ending with
/// one its code pops (whose code is in the frame outside it), nor above a
/// mark in tail position (which a mark in tail position in the frame above
/// it finds directly under its own, to replace). The last links and
/// returns to the bottom if the chain ends there, else returns through the
/// underflow. The rest of the chain is the run's. Where the innermost is,
/// and where it resumes.
fn restore(heap: &Heap, st: &mut DState, p: Pos) -> Result<(u64, u64), String> {
    let (mut recs, mut words, mut q) = (Vec::with_capacity(64), 0, p);
    while let Some((r, nq)) = step(heap, q) {
        let returns = r.returns();
        recs.push((r, returns));
        words += r.n;
        q = nq;
        if words >= RESTORE_WORDS && returns && !step(heap, q).is_some_and(|(r2, _)| r2.is_tail_mark()) {
            break;
        }
    }
    if recs.is_empty() {
        return Err("the stack cache has nothing to restore".into());
    }
    let more = step(heap, q).is_some();
    let (link, ret) = if more { (0, st.underflow) } else { (st.bottom_link, st.bottom_ret) };
    let base = place(st, &recs, words, st.stack_top, link, ret)?;
    set_cont(st, if more { q } else { END });
    st.stats.frames_restored += recs.len() as u64;
    Ok((base, recs[0].0.pc))
}

/// Frames `recs` (each with whether it is left by a return), `words` in all,
/// put on the stack ending at `end`, innermost lowest: the last linking to
/// `link` and, if left by a return, returning to `ret`; each other to the
/// next, returning as it did. Where the innermost is.
fn place(st: &DState, recs: &[(Rec, bool)], words: usize, end: u64, link: u64, ret: u64) -> Result<u64, String> {
    let base = end - 8 * words as u64;
    if base < st.stack_limit {
        return Err("stack overflow".into());
    }
    let mut fp = base;
    for (i, &(r, returns)) in recs.iter().enumerate() {
        let last = i + 1 == recs.len();
        put_frame(r, fp, if last { link } else { fp + 8 * r.n as u64 }, if last && returns { ret } else { r.w8 });
        fp += 8 * r.n as u64;
    }
    Ok(base)
}

/// Frame `r` put on the stack at `fp`, linking to `link`, its second word
/// `second`.
fn put_frame(r: Rec, fp: u64, link: u64, second: u64) {
    set_word(fp, link);
    set_word(fp + 8, second);
    // SAFETY: words of the native stack, above its limit, which no Rust
    // code holds while the call-out runs; the frame's, in its chunk.
    unsafe { std::ptr::copy_nonoverlapping(r.words.add(r.at + 2), (fp + 16) as *mut u64, r.n - 2) };
}

/// What an overflow's site says of its procedure's entry: how many of
/// REG1…REG8 hold its arguments (bits 0-7), whether the closure in `CLO` is
/// read (bit 8), whether it is variadic, its count in X9 and its arguments
/// in the state's `args` too (bit 9).
fn overflow_info(arity: usize, captures: bool) -> u64 {
    let regs = if arity == usize::MAX { 1 << 9 } else { arity.min(8) as u64 };
    regs | (captures as u64) << 8
}

/// The stack cache's overflow, from the entry of the procedure whose frame
/// (at `st.fp`, its link and return address in it) passed the limit,
/// Larceny's way: the run's other frames flushed into the heap where they
/// are, the nursery collected (which moves them out), and this frame (with
/// the marks in tail position under it) put at the cache's top, returning
/// through the underflow. A frame too large for the cache, or frames past
/// the most a run may have, overflow the stack.
fn overflow(heap: &mut Heap, st: &mut DState) -> u64 {
    let (f0, top) = (st.fp, st.stack_top);
    // The frames kept: this one, and the marks in tail position it is
    // under, which a mark in tail position in it finds directly under its
    // frame, to replace (`withmark-tail`).
    let mut keep: Vec<(u64, u64)> = Vec::new();
    for (fp, end) in frames_from(f0, top) {
        if keep.is_empty() || is_tail_mark(fp, end) {
            keep.push((fp, end));
        } else {
            break;
        }
    }
    let (outer, kept_end) = *keep.last().expect("this frame");
    let caller = word(outer);
    if !(caller > outer && caller < top && caller == kept_end) {
        return failed(st, "stack overflow".into());
    }
    let size = kept_end - f0;
    let frames: Vec<(u64, u64)> = frames_from(caller, top).collect();
    let words: u64 = frames.iter().map(|&(a, b)| (b - a) / 8).sum();
    if chain_words(heap, cont_pos(st)) + words + size / 8 > st.max_words {
        return failed(st, "stack overflow".into());
    }
    // The kept frames aside, where the flush writes its chunk's start; the
    // marks' words are values to keep.
    let mut kept: Vec<Value> = (0..size / 8).map(|i| Value(word(f0 + 8 * i))).collect();
    let last = outermost_second(st, frames.last().expect("a frame").0);
    let mut p = flush_in_place(heap, &frames, last, cont_pos(st));
    p.pc = kept[((outer - f0) / 8 + 1) as usize].raw();
    set_cont(st, p);
    st.stats.overflows += 1;
    st.stats.frames_flushed += frames.len() as u64;
    st.stats.words_flushed += words;
    // The collection: the roots, what the entry holds (`overflow_info`).
    let info = st.overflow_info;
    let variadic = info & 1 << 9 != 0;
    let n = if variadic { (st.nargs as usize).min(8) } else { (info & 0xff) as usize };
    let mut regs: Vec<Value> = (1..=n).map(|r| Value(st.kept[r])).collect();
    let mut saved: Vec<Value> = if variadic { st.args[..n].iter().map(|a| Value(*a)).collect() } else { Vec::new() };
    let mut clo: Vec<Value> = if info & 1 << 8 != 0 { vec![Value(st.kept[CLO as usize])] } else { Vec::new() };
    let mut code = [Value(st.overflow_code), Value(st.code)];
    let mut cont = [Value(st.cont)];
    {
        let mut roots: Vec<&mut [Value]> = vec![&mut regs, &mut saved, &mut clo, &mut code, &mut cont];
        // The marks' words, from the third on, in each kept frame but this.
        let mut rest: &mut [Value] = &mut kept;
        let mut at = 0u64;
        for &(fp, end) in &keep {
            let n = ((end - fp) / 8) as usize;
            let (this, more) = rest.split_at_mut(n);
            if fp != f0 {
                roots.push(&mut this[2..]);
            }
            rest = more;
            at += n as u64;
        }
        debug_assert_eq!(at * 8, size);
        heap.collect_young(&mut roots);
    }
    for (r, v) in regs.iter().enumerate() {
        st.kept[r + 1] = v.raw();
    }
    for (i, v) in saved.iter().enumerate() {
        st.args[i] = v.raw();
    }
    if let Some(c) = clo.first() {
        st.kept[CLO as usize] = c.raw();
    }
    (st.code, st.cont) = (code[1].raw(), cont[0].raw());
    // The kept frames at the cache's top, their links moved with them; the
    // outermost's to nothing, returning through the underflow.
    let to = top - size;
    for (i, v) in kept.iter().enumerate() {
        set_word(to + 8 * i as u64, v.raw());
    }
    let moved = |a: u64| a - f0 + to;
    for &(fp, _) in &keep[..keep.len() - 1] {
        set_word(moved(fp), moved(word(moved(fp))));
    }
    set_word(moved(outer), 0);
    set_word(moved(outer) + 8, st.underflow);
    (st.resume_sp, st.resume_fp) = (to, to);
    0
}

/// The stack's `frames`, innermost first, contiguous and the run's last,
/// made a chunk of the chain onto `tail` where they are (Larceny's flush in
/// place): its header and fields written below the innermost, its trailer
/// at the run's top; each frame's link its size, its second word a fixnum
/// (the outermost's `last`), its dead words 0. An object of the nursery,
/// which the collection that must follow moves out. Where the innermost
/// is, its `pc` for the caller to say.
fn flush_in_place(heap: &mut Heap, frames: &[(u64, u64)], last: u64, tail: Pos) -> Pos {
    let (lo, hi) = (frames[0].0, frames.last().expect("a frame").1);
    let rest = chain_words(heap, tail);
    set_word(lo - 8 * (CH_FRAMES - CH_NEXT) as u64, tail.chunk.raw());
    set_word(lo - 8 * (CH_FRAMES - CH_NEXT_AT) as u64, Value::fixnum(tail.at as i64).raw());
    set_word(lo - 8 * (CH_FRAMES - CH_REST) as u64, Value::fixnum(rest as i64).raw());
    let outermost = frames.len() - 1;
    for (f, &(fp, end)) in frames.iter().enumerate() {
        let mask = kept_mask(fp, end);
        let second = if f == outermost { last } else { word(fp + 8) };
        set_word(fp, Value::fixnum(((end - fp) / 8) as i64).raw());
        set_word(fp + 8, Value::fixnum(second as i64).raw());
        for (j, at) in (fp + 16..end).step_by(8).enumerate() {
            if j < 64 && mask & (1 << j) == 0 {
                set_word(at, Value::fixnum(0).raw());
            }
        }
    }
    let n = CH_FRAMES + ((hi - lo) / 8) as usize;
    let chunk = heap.vector_in_place(lo - 8 * (CH_FRAMES as u64 + 1), n);
    Pos::new(chunk, CH_FRAMES, 0)
}

/// Every frame of the run on the stack, from the one that called out (at
/// `st.fp`, the stack's pointer too), flushed where it is onto the chain,
/// leaving the stack empty: for a collection, which moves them out, after
/// which `restore` puts the innermost back. Where the innermost resumes is
/// not kept: the call-out returns to it.
fn flush_all(heap: &mut Heap, st: &mut DState) {
    debug_assert_eq!(st.fp, st.native_sp, "a call-out's frame is the stack's top");
    let frames = frames_of(st);
    let Some(&(outer, _)) = frames.last() else { return };
    let words: u64 = frames.iter().map(|&(a, b)| (b - a) / 8).sum();
    let last = outermost_second(st, outer);
    let p = flush_in_place(heap, &frames, last, cont_pos(st));
    set_cont(st, p);
    st.stats.collection_flushes += 1;
    st.stats.frames_flushed += frames.len() as u64;
    st.stats.words_flushed += words;
}

/// Whether the frame from `fp` to `end` is a mark's in tail position: a
/// control frame of `MARK_MARK` left by a return to its second word.
fn is_tail_mark(fp: u64, end: u64) -> bool {
    end - fp == CONTROL_FRAME && word(fp + 16) == MARK_MARK.raw() && word(fp + 8) != 0
}

/// A continuation's data, around `p`, the chain of its frames.
fn continuation(rt: &mut fixpt_runtime::Runtime, st: &DState, p: Pos, whole: bool) -> Value {
    let heap = &mut rt.heap;
    let regions = Value::fixnum(heap.live_regions() as i64);
    let data = heap.vector_from(&[CONT_MARK, p.chunk, Value::fixnum(p.at as i64), Value::fixnum(p.pc as i64), regions, Value::boolean(whole)]);
    native_closure(heap, Value(st.aux), &[data])
}

/// A continuation's chain.
fn continuation_pos(heap: &Heap, data: Value) -> Pos {
    Pos::new(heap.obj_ref(data, 1), heap.obj_ref(data, 2).as_fixnum() as usize, heap.obj_ref(data, 3).as_fixnum() as u64)
}

/// The whole continuation of the frames from the one that called out,
/// resumed where the state's `ret_pc` says: a native closure of the
/// continuation procedure (the state's `aux`) over its chain, the frames on
/// the stack copied onto the run's.
fn capture_whole(rt: &mut fixpt_runtime::Runtime, st: &DState) -> Value {
    let frames = frames_of(st);
    let last = outermost_second(st, frames.last().expect("a frame").0);
    let mut p = chunks_of(&mut rt.heap, &frames, last, cont_pos(st));
    p.pc = st.ret_pc;
    continuation(rt, st, p, true)
}

/// A continuation's frames, delimited by the innermost prompt for `tag`:
/// those on the stack before it; or all of them and a copy of the chain's
/// before it, in one chunk; none if no prompt for `tag` is in this run.
fn capture_delimited(rt: &mut fixpt_runtime::Runtime, st: &DState, tag: Value) -> Option<Value> {
    let frames = frames_of(st);
    if let Some(j) = frames.iter().position(|&(fp, end)| is_control(fp, end, PROMPT_MARK, tag)) {
        let last = word(frames[j - 1].0 + 8);
        let mut p = chunks_of(&mut rt.heap, &frames[..j], last, END);
        p.pc = st.ret_pc;
        return Some(continuation(rt, st, p, false));
    }
    let recs = records(&rt.heap, cont_pos(st));
    let j = recs.iter().position(|r| r.is_control(PROMPT_MARK, tag))?;
    let tail = copy_records(&mut rt.heap, &recs[..j], END);
    let last = outermost_second(st, frames.last().expect("a frame").0);
    let mut p = chunks_of(&mut rt.heap, &frames, last, tail);
    p.pc = st.ret_pc;
    Some(continuation(rt, st, p, false))
}

/// Frames `recs` of a chain copied into one new chunk onto `tail`.
fn copy_records(heap: &mut Heap, recs: &[Rec], tail: Pos) -> Pos {
    let rest = chain_words(heap, tail);
    let mut v = vec![tail.chunk, Value::fixnum(tail.at as i64), Value::fixnum(rest as i64)];
    for r in recs {
        v.extend((0..r.n).map(|k| heap.obj_ref(r.chunk, r.at + k)));
    }
    let chunk = heap.vector_from(&v);
    Pos::new(chunk, CH_FRAMES, recs.first().map_or(tail.pc, |r| r.pc))
}

/// Continuation `k` given `v`: its frames put back, and the state told to
/// resume where it was taken. A whole one replaces this run's frames (its
/// last returning where this run's outermost does) and ends the regions
/// entered since it was taken; a delimited one goes on top of the
/// continuation procedure's caller (the frame that procedure made is
/// where), its last frame returning to that caller: on the stack if it
/// fits, as it mostly does; else the caller's frames copied onto the chain,
/// and a copy of `k`'s onto them.
fn reinstate(rt: &mut fixpt_runtime::Runtime, st: &mut DState, k: Value, v: Value) -> u64 {
    let heap = &mut rt.heap;
    let data = heap.bloblet_slot(k, CLOSURE_FREE0);
    let (kp, regions, whole) = (continuation_pos(heap, data), heap.obj_ref(data, 4), heap.obj_ref(data, 5) == Value::TRUE);
    let to = if whole {
        heap.region_exit(regions.as_fixnum() as usize);
        kp
    } else {
        let (link, ret) = (word(st.fp), word(st.fp + 8));
        // Its words, then, if they fit, its frames, with no list made.
        let (mut words, mut q) = (0u64, kp);
        while let Some((r, nq)) = step(heap, q) {
            words += r.n as u64;
            q = nq;
        }
        let base = st.fp + 16 - 8 * words;
        if base >= st.stack_limit {
            let (mut fp, mut q) = (base, kp);
            while let Some((r, nq)) = step(heap, q) {
                let next = fp + 8 * r.n as u64;
                let last = next == st.fp + 16;
                put_frame(r, fp, if last { link } else { next }, if last && r.returns() { ret } else { r.w8 });
                st.stats.frames_restored += 1;
                (fp, q) = (next, nq);
            }
            (st.resume_sp, st.resume_fp, st.resume_pc, st.resume_x0) = (base, base, kp.pc, v.raw());
            return 0;
        }
        let recs: Vec<(Rec, bool)> = records(heap, kp).into_iter().map(|r| (r, r.returns())).collect();
        let below: Vec<(u64, u64)> = if link > st.fp && link < st.stack_top { frames_from(link, st.stack_top).collect() } else { Vec::new() };
        let rest = if below.is_empty() {
            cont_pos(st)
        } else {
            let last = outermost_second(st, below.last().expect("a frame").0);
            let mut p = chunks_of(heap, &below, last, cont_pos(st));
            p.pc = ret;
            p
        };
        // `k`'s last returns where the caller resumes.
        let mut p = copy_records(heap, &recs.iter().map(|r| r.0).collect::<Vec<_>>(), rest);
        let len = heap.obj_len(p.chunk);
        let mut at = CH_FRAMES;
        while at < len {
            let n = heap.obj_ref(p.chunk, at).as_fixnum() as usize;
            if at + n == len {
                heap.obj_set(p.chunk, at + 1, Value::fixnum(rest.pc as i64));
            }
            at += n;
        }
        p.pc = kp.pc;
        p
    };
    match restore(heap, st, to) {
        Ok((fp, pc)) => {
            (st.resume_sp, st.resume_fp, st.resume_pc, st.resume_x0) = (fp, fp, pc, v.raw());
            0
        }
        Err(why) => failed(st, why),
    }
}

/// The marks for `key` in this run, innermost first: on the stack, then in
/// the chain.
fn run_marks(heap: &Heap, st: &DState, key: Value) -> Vec<Value> {
    let mut out: Vec<Value> = frames(st).filter(|&(fp, end)| is_control(fp, end, MARK_MARK, key)).map(|(fp, _)| Value(word(fp + 32))).collect();
    out.extend(chain_marks(heap, cont_pos(st), key));
    out
}

/// The marks for `key` in the chain from `p`, newest first.
fn chain_marks(heap: &Heap, p: Pos, key: Value) -> Vec<Value> {
    records(heap, p).into_iter().filter(|r| r.is_control(MARK_MARK, key)).map(|r| r.word(2)).collect()
}

/// The marks for `key` continuation `k` took, innermost first: a native
/// continuation's, from its chain; a cellular one's, from its return
/// stack's entries. None if `k` is neither.
fn marks_of(heap: &Heap, k: Value, key: Value) -> Option<Vec<Value>> {
    if let Some(data) = heap.native_continuation_of(k) {
        return Some(chain_marks(heap, continuation_pos(heap, data), key));
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
    // A frame too large for a mask: every slot.
    if head.as_fixnum() < 0 {
        return vec![(fp + 24, n - 1)];
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

