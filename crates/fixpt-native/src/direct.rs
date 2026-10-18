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
//! | values across a call | the frame's slots, from `[x29, #24]`: its values, the code  |
//! |                      | bloblet and the closure, then its raw `f64`s (`raw_slots`)  |
//! | the frame's stack map | `[x29, #16]`: a fixnum, the mask of the values traced, and |
//! |                      | its count of fields (`MAP_BITS`, `frame_shape`)            |
//! | the frame's header   | `[x29, #-8]`: room for its bloblet's header (`STUB_FRAME`)  |
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
use fixpt_heap::layout::cellular::{CLOSURE_FREE0, CLOSURE_WORD, CODE_SOURCE, GLOBAL_FIELDS, GLOBAL_WRITES, ROUTINES, WORD_CELL0, WORD_TWIN};
use fixpt_heap::layout::regcode::OPS;
use fixpt_heap::{Heap, Value};
use std::collections::HashMap;
use std::mem::offset_of;

mod reps;
mod declare;
pub use declare::native_convention;
mod x64;
mod fx;
pub use fx::{fx_abandon, FxCompile, FxEmitted, FxRequest};
pub use x64::{fx26_direct_module, fx26_direct_module_sig, oracle as oracle_x64};
pub use reps::oracle as reps_oracle;
use reps::{Convert, RawOp, Rep};

/// Whether the machine is x86_64's (`x64`): every other code is arm64's.
const X86: bool = cfg!(target_arch = "x86_64");

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
const X12: Reg = 12;

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
    /// this run's frames, older than any on the stack, in the heap, each a
    /// native frame linked to the next out (`TODO.md` §91): the innermost
    /// (or `#f`), and where it resumes; and the most words a run's frames
    /// may take.
    cont: u64,
    /// How many words of frames the chain at `cont` holds (`TODO.md` §91):
    /// what bounds the run's frames (`max_words`).
    cont_words: u64,
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
    /// Fuel not yet given out: `fuel` is a time slice of it
    /// (`fixpt_runtime::sched::slice`), at whose end a poll takes the next
    /// and asks whether the scheduler would have another task run
    /// (`Callout::Poll`).
    reserve: u64,
    /// The machine's routines for code a program made (`TODO.md` §97,
    /// `declare.rs`), where they run: a poll at a spent time slice
    /// (`common_poll`), a pair made (`common_cons`), and a bloblet
    /// (`common_bloblet`).
    poll: u64,
    cons: u64,
    bloblet: u64,
    /// x86_64's REG4…REG8 (`x64`), by number: that machine has registers
    /// for only three.
    regs: [u64; 9],
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
const TRAPS: [&str; 6] = ["", "evaluation step limit exceeded", "stack overflow", "a primitive failed", "car or cdr of a non-pair", "division by zero"];
const OUT_OF_FUEL: u32 = 1;
/// The call-out a poll makes at a time slice's end (`Callout::Poll`).
const POLL: usize = 4;
const POLL_DONE: usize = 5;
const REINSTATE: usize = 7;
const CONS: usize = 8;
const BLOBLET: usize = 9;
const FAILED: usize = 6;
/// A poll's frame (`emit_poll`), laid out as a procedure's: its link, its
/// second word, its map, eleven values (x0…x8 where they hold values, the
/// closure, the code bloblet), then the raw words (x0…x8 where they hold
/// raw bits, and x9), and a word to align it.
const POLL_FRAME: u64 = 208;
const POLL_FIELDS: u64 = 14;
const POLL_RAW0: u32 = 24 + 8 * 11;

/// A poll whose slice is spent (`emit_poll`): where its way out is, and
/// where the procedure goes on; which of x0…x8 hold values to keep, and
/// which raw bits; whether the closure lives only in `CLO` (no frame, and
/// the code reads it); and whether the procedure has its frame, whose map
/// for here (`map`) is stored first.
struct NPoll {
    out: Label,
    back: Label,
    values: Vec<Reg>,
    raws: Vec<Reg>,
    clo: bool,
    map: Option<i64>,
}

/// A poll's way out, at a time slice's end: out of fuel (as before) if the
/// reserve is spent; else a frame of its own, mapped as a procedure's,
/// holding what is live (`NPoll`), the call-out that gives the next slice
/// and says whether the scheduler would have another task run, and if so
/// its `preempt` called from here, as any procedure is, so that a capture
/// in it takes this frame as it takes any. Back: what was kept put back,
/// the frame popped, and on: to `back` by its return if the procedure has
/// a frame (its second word, which a restore may have made the underflow
/// that brings the procedure's frame back first); else by a branch, the
/// link the procedure's own again.
fn emit_poll(a: &mut Asm, p: &NPoll, stubs: &mut Vec<(Label, u32)>) {
    a.bind(p.out);
    a.e(ldr(X16, ST, st_off(offset_of!(DState, reserve))));
    a.e(cmp_imm(X16, 0));
    let spent = a.label();
    stubs.push((spent, OUT_OF_FUEL));
    a.to(spent, Fix::If(Cond::Eq));
    if let Some(m) = p.map {
        a.es(&mov_imm64(X16, Value::fixnum(m).raw()));
        a.e(str(X16, FRAME, 16));
        a.to(p.back, Fix::Adr(X17));
        push_frame(a, X17, POLL_FRAME);
    } else {
        push_frame(a, LINK, POLL_FRAME);
    }
    let mut mask = 1u64 << 10;
    for &r in &p.values {
        mask |= 1 << r;
    }
    if p.clo {
        mask |= 1 << 9;
    }
    a.es(&mov_imm64(X16, Value::fixnum((POLL_FIELDS << MAP_BITS | mask) as i64).raw()));
    a.e(str(X16, FRAME, 16));
    for &r in &p.values {
        a.e(str(r, FRAME, 24 + 8 * r as u32));
    }
    if p.clo {
        a.e(str(CLO, FRAME, 24 + 8 * 9));
    }
    ldr_field(a, X16, 1);
    a.e(str(X16, FRAME, 24 + 8 * 10));
    for &r in &p.raws {
        a.e(str(r, FRAME, POLL_RAW0 + 8 * r as u32));
    }
    a.e(str(X9, FRAME, POLL_RAW0 + 8 * 9));
    call_out(a, POLL);
    a.e(ldr(FUEL, ST, st_off(offset_of!(DState, fuel))));
    a.e(ldr(CLO, ST, st_off(offset_of!(DState, aux))));
    let resume = a.label();
    a.e(cmp_imm(CLO, 0));
    a.to(resume, Fix::If(Cond::Eq));
    a.e(ldur(X16, CLO, field_off(CLOSURE_WORD)));
    a.e(add(X16, X16, DELTA));
    a.e(movz(X9, 0, 0));
    a.e(blr(X16));
    call_out(a, POLL_DONE);
    a.bind(resume);
    for &r in &p.values {
        a.e(ldr(r, FRAME, 24 + 8 * r as u32));
    }
    if p.clo {
        a.e(ldr(CLO, FRAME, 24 + 8 * 9));
    }
    for &r in &p.raws {
        a.e(ldr(r, FRAME, POLL_RAW0 + 8 * r as u32));
    }
    a.e(ldr(X9, FRAME, POLL_RAW0 + 8 * 9));
    pop_frame(a, POLL_FRAME);
    if p.map.is_some() {
        a.e(ret());
    } else {
        a.to(p.back, Fix::B);
    }
}
const STACK_OVERFLOW: u32 = 2;
const PRIM_FAILED: u32 = 3;
const NOT_A_PAIR: u32 = 4;
const DIVIDED_BY_ZERO: u32 = 5;

/// What a call-out does: `cons`; a runtime primitive of `n` arguments; a
/// native closure over `n` values of the code in the state's `aux`.
#[derive(Copy, Clone)]
enum Callout {
    Cons,
    /// A plain bloblet of `bytes` suffix bytes and `fields` fields (two
    /// fixnums), for code a program made (`common_bloblet`); refused, by
    /// the trap, for sizes `%make-bloblet-filled` refuses.
    Bloblet,
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
    /// of the code in the state's `aux`, the continuation procedure; `once`,
    /// one-shot (`callone`, `TODO.md` §98).
    Capture { whole: bool, once: bool },
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
    /// A time slice's end, at a poll (`poll_frame`): the next slice given,
    /// and in `aux` the scheduler's `preempt` if it would have another task
    /// run, for the poll to call, else 0. And a collection, if one is due:
    /// the poll's frame holds what is live (`emit_poll`, `common_poll`), as
    /// a call's does. The safepoint a loop comes to that allocates only by
    /// quiet call-outs (a box made past the nursery's end for a call
    /// through a procedure value), which grew the heap without bound when
    /// none collected (`TODO.md` §102): a slice is short enough
    /// (`sched::SLICE` polls) that its end comes soon after.
    Poll,
    /// That call returned (`sched::preempt_done`). No collection.
    PollDone,
    /// A trap, from the common trap: if the task is of a monitored process,
    /// an abort to the scheduler's prompt made of it (`sched::task_failed`,
    /// `abort_to`), and `aux` 1; else `aux` 0, and the run leaves. No
    /// collection.
    Failed,
}

impl Callout {
    fn arity(self) -> usize {
        match self {
            Callout::Cons | Callout::Bloblet | Callout::FieldRef | Callout::Abort | Callout::Reinstate | Callout::FirstMark | Callout::MarksOf => 2,
            Callout::Capture { whole, .. } => if whole { 1 } else { 2 },
            Callout::CurrentMarks | Callout::Box { .. } | Callout::Unbox | Callout::BoxF64 => 1,
            Callout::Foreign | Callout::ClosureAny | Callout::Rest | Callout::Underflow | Callout::Overflow | Callout::Poll | Callout::PollDone | Callout::Failed => 0,
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
    poll: u64,
    cons: u64,
    bloblet: u64,
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
/// of the same code over the same values, or why not. So too an adapter
/// cellular code made (`nclosure`): what it calls, compiled. Any other
/// native closure is itself.
pub fn compile_closure(heap: &mut Heap, closure: Value) -> Result<Value, String> {
    if DirectMachine::compiled_of(heap, closure).is_some() && heap.adapted(closure).is_none() {
        return Ok(closure);
    }
    with_machine(|m| m.compile(heap, closure).map(|procs| procs[0].1.closure))?
}

/// A runtime's `adapt` (`%fx26-convert`, `nclosure`): an adapter of `f`,
/// to the native convention if `native`, else to the cellular one, of
/// `arity` arguments (the cellular adapter's call passes them; native
/// code passes its count in `x9` at every call, Larceny's way, so the
/// native adapter needs none). To the native convention, a native closure
/// over `f` whose code calls it as native code calls what is not native
/// code, through the machine's `common_foreign`, in a tail call, the
/// count as its caller passed it:
///
/// ```text
/// ldur x10, [x10, #free 0]    the closure called: now `f`
/// ldr  x16, [x24, #foreign]
/// br   x16
/// ```
pub fn adapt(rt: &mut fixpt_runtime::Runtime, f: Value, arity: usize, native: bool) -> Result<Value, String> {
    let heap = &mut rt.heap;
    if !native {
        return Ok(fixpt_engine::cellular::cellular_adapter(heap, f, arity));
    }
    // The code, made once and shared (`Heap::adapter_code`), so that an
    // adapter is known by it (`Heap::adapted`).
    let blob = match heap.adapter_code() {
        Some(b) => b,
        None => {
            let bytes = if X86 { x64::adapter() } else { crate::arm64::bytes(&adapter_code()) };
            let blob = heap.make_code_bloblet(const { fixpt_heap::layout::kind("bloblet") }, 1, bytes.len(), false);
            heap.set_bloblet_slot(blob, 1, blob);
            heap.set_bloblet_bytes(blob, 0, &bytes).map_err(|e| format!("{e:?}"))?;
            heap.flush_code(blob);
            crate::symbols::note(heap.code_exec_address(blob), bytes.len(), "native convention: an adapter");
            heap.set_adapter_code(blob);
            blob
        }
    };
    Ok(native_closure(heap, blob, &[f]))
}

/// The native adapter's code (`adapt`), the same for every adapter.
fn adapter_code() -> Vec<u32> {
    let mut a = Asm::new();
    a.e(ldur(CLO, CLO, field_off(CLOSURE_FREE0)));
    a.e(ldr(X16, ST, st_off(offset_of!(DState, foreign))));
    a.e(br(X16));
    a.finish().expect("no labels")
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
const PROMPT_MARK: Value = Value::from_raw(Value::UNBOUND.raw() + (1 << 8));
const MARK_MARK: Value = Value::from_raw(Value::UNBOUND.raw() + (2 << 8));
const CONT_MARK: Value = fixpt_heap::NATIVE_CONT_MARK;
/// A prompt's frame, and a mark's: the link, the landing (for a mark, 0),
/// the marker, the tag and handler (the key and value), and the regions
/// live (for a mark, 0).
const CONTROL_FRAME: u64 = 64;
/// Every native frame is laid out as its bloblet will be, once flushed
/// into the heap (`TODO.md` §91, `docs/object-model.md`): a header word
/// below its link (at `[x29, #-8]`), then its link, its second word (the
/// return address, or a control frame's), the rest of its values, and its
/// raw words, its suffix. No trailer: each word of a frame counts against
/// the stack cache (a deep recursion that fits it no longer would), and a
/// trailer is not a bloblet's hard invariant. On the stack the header is
/// only room; the frame's words, its *region*, run from `x29 - 8` to the
/// next frame's. A stub's frame is `[header][link][return]`, and a word to
/// align it.
const STUB_FRAME: u64 = 32;
/// Where in a frame's region its link, its second word and its third (a
/// procedure's stack map, a control frame's marker) are.
const R_LINK: u64 = 8;
const R_SECOND: u64 = 16;
const R_HEAD: u64 = 24;
/// The bits of a procedure frame's stack map that say which values are
/// live; above them, its count of fields (`frame_shape`). A frame of more
/// values has no map: its map word is minus its count of fields.
const MAP_BITS: u32 = 48;

fn st_off(f: usize) -> u32 {
    f as u32
}

/// The native stack is the heap's (`Heap::native_stack`), at the nursery's
/// top; a run's stack cache is part of it, with room below its limit for
/// the frame that finds it has passed it.
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
/// word, name and arity, its code bloblet's fields, and its code, in bytes,
/// of which the first `len` are its own (the rest, its traps').
struct Proc {
    word: Value,
    rw: Value,
    name: String,
    arity: usize,
    fields: Vec<Field>,
    code: Vec<u8>,
    len: usize,
    /// A global's procedure, which may be called through its cell instead.
    global: bool,
    /// The parameters it takes raw (`reps::raw_params`), once known.
    params: Option<u8>,
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
    poll: Offset,
    cons: Offset,
    bloblet: Offset,
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
/// many of its bytes are its own code, its arity, and a native closure of it
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
        if !crate::NATIVE_CONVENTION_AVAILABLE {
            return Err(crate::UNAVAILABLE.into());
        }
        fixpt_runtime::crossing::set_foreign_marks(marks_of);
        let mut space = CodeSpace::new(8 << 20).map_err(|e| e.to_string())?;
        // The machine's own code, in bytes, for this instruction set.
        let a64 = |w: Vec<u32>| crate::arm64::bytes(&w);
        // Call-out 0: what is not native code, called (`common_foreign`);
        // 1: a closure made (`common_closure`); 2 and 3: the stack cache's
        // underflow and overflow (`common_underflow`, `common_overflow`);
        // 4 and 5: a time slice's end at a poll, and its call of `preempt`
        // returned (`POLL`, `POLL_DONE`); 6: a trap (`FAILED`); 7: a
        // continuation given a value (`REINSTATE`); 8: a pair made, for
        // code a program made (`common_cons`, `CONS`); 9: a bloblet made,
        // for it too (`common_bloblet`, `BLOBLET`).
        let callouts = vec![
            Callout::Foreign,
            Callout::ClosureAny,
            Callout::Underflow,
            Callout::Overflow,
            Callout::Poll,
            Callout::PollDone,
            Callout::Failed,
            Callout::Reinstate,
            Callout::Cons,
            Callout::Bloblet,
        ];
        let pieces: [(Vec<u8>, &str); 10] = if X86 {
            [
                (x64::trampoline(), "trampoline"),
                (x64::mark_ret(), "a mark's return"),
                (x64::common_trap(), "common trap"),
                (x64::common_foreign(0), "common foreign call"),
                (x64::common_closure(1), "common closure"),
                (x64::common_underflow(2), "stack cache underflow"),
                (x64::common_overflow(3), "stack cache overflow"),
                (x64::common_poll(), "common poll"),
                (x64::common_cons(), "common cons"),
                (x64::common_bloblet(), "common bloblet"),
            ]
        } else {
            [
                (a64(trampoline()), "trampoline"),
                (a64(vec![ldp(FRAME, LINK, SP, 8), add_imm(SP, SP, CONTROL_FRAME as u32), ret()]), "a mark's return"),
                (a64(common_trap()), "common trap"),
                (a64(common_foreign(0)), "common foreign call"),
                (a64(common_closure(1)), "common closure"),
                (a64(common_underflow(2)), "stack cache underflow"),
                (a64(common_overflow(3)), "stack cache overflow"),
                (a64(common_poll()), "common poll"),
                (a64(common_cons()), "common cons"),
                (a64(common_bloblet()), "common bloblet"),
            ]
        };
        let mut at = [0; 10];
        for (k, (code, what)) in pieces.iter().enumerate() {
            at[k] = space.alloc(code.len(), 16).ok_or_else(|| format!("no room for the {what}"))?;
            space.write(at[k], code);
            space.flush(at[k], code.len());
            crate::symbols::note(space.exec_addr(at[k]), code.len(), &format!("native convention: {what}"));
        }
        let [entry, mark_ret, trap_stub, foreign, closure, underflow, overflow, poll, cons, bloblet] = at;
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
            poll,
            cons,
            bloblet,
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
            let mut c = Compiling { heap: &*heap, procs: Vec::new(), by_word: HashMap::new(), queue: Vec::new(), callouts: &mut self.callouts, resume: None, refused, native_masks: HashMap::new() };
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
        install(heap, &procs, first, &free)
    }
}

/// `procs`, compiled, each in a code bloblet of its own: what they are,
/// the first (`first`) as a native closure over `free`.
fn install(heap: &mut Heap, procs: &[Proc], first: usize, free: &[Value]) -> Result<Vec<(String, Compiled)>, String> {
    // Every bloblet first, then their fields, which refer to each other.
    // Nothing here collects, so the values held do not move.
    let blobs: Vec<Value> =
        procs.iter().map(|p| heap.make_code_bloblet(const { fixpt_heap::layout::kind("bloblet") }, p.fields.len(), p.code.len(), false)).collect();
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
        let bytes = &p.code;
        heap.set_bloblet_bytes(blob, 0, bytes).map_err(|e| format!("{e:?}"))?;
        heap.flush_code(blob);
        if crate::symbols::enabled() {
            crate::symbols::note(heap.code_exec_address(blob), bytes.len(), &format!("native {}", p.name));
        }
    }
    let entry = native_closure(heap, blobs[first], free);
    Ok(procs
        .iter()
        .zip(&blobs)
        .enumerate()
        .map(|(i, (p, &code))| (p.name.clone(), Compiled { code, len: p.len, arity: p.arity, closure: if i == first { entry } else { Value::FALSE } }))
        .collect())
}

impl DirectMachine {
    /// A native closure, as what it runs: its code, all of it, and the
    /// closure; its arity is not recorded, so a call of it is not checked.
    pub fn compiled_of(heap: &Heap, closure: Value) -> Option<Compiled> {
        if !closure.is_bloblet() || heap.bloblet_kind(closure) != const { fixpt_heap::layout::kind("native-closure") } {
            return None;
        }
        let code = heap.bloblet_slot(closure, CLOSURE_WORD);
        Some(Compiled { code, len: heap.bloblet_head(code).bytes, arity: usize::MAX, closure })
    }

    /// Call `p` with `args`, in at most about `fuel` steps, in `rt`, whose
    /// heap its call-outs allocate in, collecting when they must.
    pub fn call(&mut self, rt: &mut fixpt_runtime::Runtime, p: Compiled, args: &[Value], fuel: u64) -> Result<Value, DirectTrap> {
        // The heap's native stack (`Heap::native_stack`), with a little room
        // at its top, where the outermost frame flushed there points.
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
            poll: self.space.exec_addr(self.poll) as u64,
            cons: self.space.exec_addr(self.cons) as u64,
            bloblet: self.space.exec_addr(self.bloblet) as u64,
            table: self.callouts.as_ptr() as u64,
            cache_words: self.cache_words,
            max_words: self.max_words,
        }
    }

    /// `p`'s instructions, as they are in its code bloblet: arm64's.
    pub fn instructions(&self, heap: &Heap, p: Compiled) -> Vec<u32> {
        let bytes = heap.bloblet_bytes(p.code);
        (0..p.len / 4).map(|i| u32::from_le_bytes(bytes[4 * i..4 * i + 4].try_into().expect("four bytes"))).collect()
    }

    /// `p`'s own code, an instruction to a line, for this machine's
    /// instruction set.
    pub fn lines(&self, heap: &Heap, p: Compiled) -> Vec<String> {
        code_lines(&heap.bloblet_bytes(p.code)[..p.len])
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
        cont_words: 0,
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
    // Fuel in time slices (`DState::reserve`).
    let slice = fixpt_runtime::sched::slice();
    if st.fuel > slice {
        (st.fuel, st.reserve) = (slice, st.fuel - slice);
    }
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
    (st.poll, st.cons, st.bloblet) = (r.poll, r.cons, r.bloblet);
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
    Ok(Value::from_raw(v))
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
    // A task of a monitored process: its failure an abort to the
    // scheduler's prompt (`Callout::Failed`), on from there.
    call_out(&mut a, FAILED);
    let gone = a.label();
    a.e(ldr(X9, ST, st_off(offset_of!(DState, aux))));
    a.e(cmp_imm(X9, 0));
    a.to(gone, Fix::If(Cond::Eq));
    resume(&mut a);
    a.bind(gone);
    leave(&mut a);
    a.finish().expect("labels bound")
}

/// The common poll, for code a program made (`TODO.md` §97): from where its
/// fuel ran out, by `blr`, every value it keeps in its frame, whose stack
/// map it has stored, and none in registers but the pinned ones. A stub's
/// frame; the next slice taken (`Callout::Poll`), or, with none left, the
/// trap for fuel spent; the scheduler's `preempt` called if it would have
/// another task run; and back, every register but the pinned ones lost.
/// One for the machine.
fn common_poll() -> Vec<u32> {
    let mut a = Asm::new();
    a.e(ldr(X16, ST, st_off(offset_of!(DState, reserve))));
    let spent = a.label();
    a.e(cmp_imm(X16, 0));
    a.to(spent, Fix::If(Cond::Eq));
    push_frame(&mut a, LINK, STUB_FRAME);
    call_out(&mut a, POLL);
    a.e(ldr(FUEL, ST, st_off(offset_of!(DState, fuel))));
    a.e(ldr(CLO, ST, st_off(offset_of!(DState, aux))));
    let back = a.label();
    a.e(cmp_imm(CLO, 0));
    a.to(back, Fix::If(Cond::Eq));
    a.e(ldur(X16, CLO, field_off(CLOSURE_WORD)));
    a.e(add(X16, X16, DELTA));
    a.e(movz(X9, 0, 0));
    a.e(blr(X16));
    call_out(&mut a, POLL_DONE);
    a.bind(back);
    pop_frame(&mut a, STUB_FRAME);
    a.e(ret());
    // The trap's site the poll's call, as for a site's own stub.
    a.bind(spent);
    a.e(movz(X9, OUT_OF_FUEL, 0));
    a.e(ldr(X16, ST, st_off(offset_of!(DState, trap_stub))));
    a.e(br(X16));
    a.finish().expect("labels bound")
}

/// The common cons, for code a program made (`TODO.md` §97): from its
/// call, by `blr`, the car in X1 and the cdr in X2, values; every other
/// value it keeps in its frame, whose stack map it has stored. A stub's
/// frame, and call-out `CONS`, which may collect (the two are roots); the
/// pair in `RESULT`, every register but the pinned ones lost.
fn common_cons() -> Vec<u32> {
    let mut a = Asm::new();
    push_frame(&mut a, LINK, STUB_FRAME);
    let args = offset_of!(DState, args) as u32;
    a.e(str(1, ST, args));
    a.e(str(2, ST, args + 8));
    call_out(&mut a, CONS);
    pop_frame(&mut a, STUB_FRAME);
    a.e(ret());
    a.finish().expect("labels bound")
}

/// The common bloblet, for code a program made (`TODO.md` §97): from its
/// call, by `blr`, the suffix's bytes in X1 and the count of fields in X2,
/// fixnums; every value it keeps in its frame, as for `common_cons`. A
/// stub's frame, and call-out `BLOBLET`, which may collect; a plain bloblet
/// in `RESULT`, its trailer field 1, fields 2 on the fixnum 0, its suffix
/// zero; or, for sizes it refuses, the trap.
fn common_bloblet() -> Vec<u32> {
    let mut a = Asm::new();
    push_frame(&mut a, LINK, STUB_FRAME);
    let args = offset_of!(DState, args) as u32;
    a.e(str(1, ST, args));
    a.e(str(2, ST, args + 8));
    call_out(&mut a, BLOBLET);
    a.e(ldr(X9, ST, st_off(offset_of!(DState, trap))));
    let (failed, stub) = (a.label(), a.label());
    a.e(cmp_imm(X9, 0));
    a.to(failed, Fix::If(Cond::Ne));
    pop_frame(&mut a, STUB_FRAME);
    a.e(ret());
    a.bind(failed);
    a.to(stub, Fix::Bl);
    a.bind(stub);
    a.e(movz(X9, PRIM_FAILED, 0));
    a.e(ldr(X16, ST, st_off(offset_of!(DState, trap_stub))));
    a.e(br(X16));
    a.finish().expect("labels bound")
}

/// What `%make-bloblet-filled` accepts: a suffix of 0 to 4 GiB, and a
/// count of fields under 2^40; else none.
fn bloblet_sizes(bytes: Value, fields: Value) -> Option<(usize, usize)> {
    let (b, f) = (bytes.is_fixnum().then(|| bytes.as_fixnum())?, fields.is_fixnum().then(|| fields.as_fixnum())?);
    ((0..=u32::MAX as i64).contains(&b) && (0..1 << 40).contains(&f)).then_some((b as usize, f as usize))
}

/// The common call of what is not native code: from a code's stub for
/// such a call, with the arguments' count in X9 and the callee in CLO (a
/// `bl` or, in tail position, a `b`, so the return address is where to go
/// back to): a frame, the arguments into the state, call-out `n` (a
/// `Callout::Foreign`), and back with its value; or, if it failed, the
/// trap. One for the machine.
/// A frame of `size` bytes pushed (a multiple of 16, at most 4095): its
/// link and `second` stored, `x29` at its link, its header word below.
fn push_frame(a: &mut Asm, second: Reg, size: u64) {
    a.e(sub_imm(SP, SP, size as u32));
    a.e(stp(FRAME, second, SP, 8));
    a.e(add_imm(FRAME, SP, 8));
}

/// The frame of `size` bytes on top popped: the link and return address
/// back.
fn pop_frame(a: &mut Asm, size: u64) {
    a.e(ldp(FRAME, LINK, SP, 8));
    a.e(add_imm(SP, SP, size as u32));
}

fn common_foreign(n: usize) -> Vec<u32> {
    let mut a = Asm::new();
    push_frame(&mut a, LINK, STUB_FRAME);
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
    pop_frame(&mut a, STUB_FRAME);
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
    push_frame(&mut a, LINK, STUB_FRAME);
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
    pop_frame(&mut a, STUB_FRAME);
    a.e(ret());
    a.bind(failed);
    a.to(stub, Fix::Bl);
    a.bind(stub);
    a.e(movz(X9, PRIM_FAILED, 0));
    a.e(ldr(X16, ST, st_off(offset_of!(DState, trap_stub))));
    a.e(br(X16));
    a.finish().expect("labels bound")
}

/// The continuation procedure's code (`Compiling::resume_proc`), call-out
/// `n` its `Callout::Reinstate`.
fn continuation_code(n: usize) -> Vec<u32> {
    let mut a = Asm::new();
    push_frame(&mut a, LINK, STUB_FRAME);
    let args = offset_of!(DState, args) as u32;
    a.e(str(1, ST, args));
    a.e(str(CLO, ST, args + 8));
    call_out(&mut a, n);
    let failed = a.label();
    a.e(ldr(X9, ST, st_off(offset_of!(DState, trap))));
    a.e(cmp_imm(X9, 0));
    a.to(failed, Fix::If(Cond::Ne));
    resume(&mut a);
    a.bind(failed);
    a.e(str(FUEL, ST, st_off(offset_of!(DState, fuel))));
    leave(&mut a);
    a.finish().expect("placed")
}

/// `continuation_code`, in bytes, for this instruction set.
fn continuation_bytes(n: usize) -> Vec<u8> {
    if X86 { x64::continuation_code(n) } else { crate::arm64::bytes(&continuation_code(n)) }
}

/// The continuation procedure as a code bloblet of its own, for a
/// continuation taken where no code gave it one: at a call of what is not
/// native code (`capture_foreign`).
fn continuation_bloblet(heap: &mut Heap) -> Value {
    let bytes = continuation_bytes(REINSTATE);
    let blob = heap.make_code_bloblet(const { fixpt_heap::layout::kind("bloblet") }, 2, bytes.len(), false);
    heap.set_bloblet_slot(blob, 1, blob);
    heap.set_bloblet_slot(blob, 2, Value::FALSE);
    heap.set_bloblet_bytes(blob, 0, &bytes).expect("room for its code");
    heap.flush_code(blob);
    blob
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
    /// What `native_params` found of each native closure's code, by the
    /// code bloblet: once a compile, not at every call.
    native_masks: HashMap<u64, Option<u8>>,
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
        let code = continuation_bytes(REINSTATE);
        let q = self.procs.len();
        self.procs.push(Proc { word: Value::FALSE, rw: Value::FALSE, name: "continuation".into(), arity: 1, fields: vec![Field::Myself, Field::Const(Value::FALSE)], len: code.len(), code, global: false, params: Some(0) });
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
        let variadic = h.bloblet_slot(rw, WORD_CELL0).as_fixnum() as usize == const { fixpt_heap::layout::regcode::op("vargs") };
        let arity = if variadic { usize::MAX } else { h.bloblet_slot(rw, WORD_CELL0 + 1).as_fixnum() as usize };
        let p = self.procs.len();
        self.procs.push(Proc { word, rw, name: self.name(word), arity, fields: vec![Field::Myself, Field::Const(word)], code: Vec::new(), len: 0, global: false, params: None });
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
        // An adapter cellular code made (`nclosure`): what it calls.
        let v = h.adapted(v).unwrap_or(v);
        if !v.is_bloblet() || h.bloblet_kind(v) != const { fixpt_heap::layout::kind("cellular-closure") } {
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
        // Made native by an earlier compile (a definition a form before),
        // taking some parameters raw: bound as it is, its raw parameters
        // known (`native_params`), so a call passes them raw, as to a
        // procedure compiled here. One that takes none is called through
        // the cell, which costs less than the guard.
        if self.heap.bloblet_head(cell).fields >= GLOBAL_FIELDS && self.native_params(v).is_some_and(|m| m != 0) {
            return Ok(Field::Const(v));
        }
        Ok(Field::Cell(cell))
    }

    /// The parameters procedure `q` takes raw (`reps::raw_params`), from its
    /// register code: what a call of it known where the call is compiled
    /// passes raw, entering past its unboxing of them (`raw_entry_skip`).
    fn params_of(&mut self, q: usize) -> u8 {
        if let Some(m) = self.procs[q].params {
            return m;
        }
        let m = register_params(self.heap, self.procs[q].rw);
        self.procs[q].params = Some(m);
        m
    }

    /// If `v` is a native closure of code this compiler made from register
    /// code (in an earlier compile: a global defined a form before), the
    /// parameters that code takes raw, as its own compile found them
    /// (`register_params` of its source's register word, the same each
    /// time). Its code's field 1 is itself and field 2 its cellular word
    /// (`CODE_SOURCE`), whose twin is register code; and its suffix is not
    /// frozen, as code a program sealed (`seal-code`) is, whose fields say
    /// nothing of how it takes its arguments.
    fn native_params(&mut self, v: Value) -> Option<u8> {
        let h = self.heap;
        if !v.is_bloblet() || h.bloblet_kind(v) != const { fixpt_heap::layout::kind("native-closure") } {
            return None;
        }
        let code = h.bloblet_slot(v, CLOSURE_WORD);
        if let Some(&m) = self.native_masks.get(&code.raw()) {
            return m;
        }
        let m = Self::code_params(h, code);
        self.native_masks.insert(code.raw(), m);
        m
    }

    /// `native_params` of code bloblet `code`.
    fn code_params(h: &Heap, code: Value) -> Option<u8> {
        if !h.is_code_bloblet(code) || h.bloblet_head(code).suffix_frozen || h.bloblet_head(code).fields < CODE_SOURCE || h.bloblet_slot(code, 1) != code {
            return None;
        }
        let word = h.bloblet_slot(code, CODE_SOURCE);
        if !h.is_cellular_word(word) || !h.is_register_word(h.bloblet_slot(word, WORD_TWIN)) {
            return None;
        }
        Some(register_params(h, h.bloblet_slot(word, WORD_TWIN)))
    }

    /// One procedure's code, from its register word.
    fn procedure(&mut self, p: usize) -> Result<(), String> {
        if X86 {
            return self.procedure_x64(p);
        }
        let h = self.heap;
        let (word, rw) = (self.procs[p].word, self.procs[p].rw);
        let cells = register_cells(h, rw);
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
        if frame.is_some_and(|m| 32 + 8 * (m + 2) > 4080) {
            return decline("a frame too large".into());
        }
        // The slots only `f64` operations read hold the `f64` raw
        // (`reps::raw_slots`, `TODO.md` §91): kept after the frame's values,
        // the code bloblet and the closure, as its bloblet's suffix, which
        // no collection traces. Each slot's place, from `x29`.
        let prim_name = |p: usize| fixpt_runtime::PRIMITIVES.get(p).map_or("?", |d| d.name);
        let raw = frame.map_or(Vec::new(), |m| reps::raw_slots(&cells, &starts, &prim_name, m));
        let values = raw.iter().filter(|r| !**r).count() as u32;
        // The parameters it takes raw (`reps::raw_params`): unboxed at its
        // entry, past which a call that knows this procedure comes, with
        // them raw (`raw_entry_skip`); and, for each call of a procedure
        // known here, that one's.
        let params = self.params_of(p);
        let mut callees = vec![0u8; starts.len()];
        for &j in &starts {
            let Some(c) = called(j) else { continue };
            let q = match op_at(j) {
                "global" => match self.global_value(cells[j + 1]).map_err(|e| format!("`{name}` calls {e}"))? {
                    Field::Code(q) => Some(q),
                    Field::Const(v) => {
                        let si = starts.iter().position(|&s| s == c).expect("an instruction");
                        callees[si] = self.native_params(v).unwrap_or(0);
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
                let si = starts.iter().position(|&s| s == c).expect("an instruction");
                callees[si] = self.params_of(q);
            }
        }
        let (slot_off, value_index) = {
            let (mut v, mut r) = (0u32, 0u32);
            let mut offs = Vec::new();
            let mut index = Vec::new();
            for &is_raw in &raw {
                if is_raw {
                    offs.push(24 + 8 * (values + 2 + r));
                    index.push(None);
                    r += 1;
                } else {
                    offs.push(24 + 8 * v);
                    index.push(Some(v));
                    v += 1;
                }
            }
            (offs, index)
        };
        // A frame of more values than its stack map has bits for has none:
        // all its values are traced, and cleared as it is made.
        let unmapped = frame.is_some() && values + 2 > MAP_BITS;
        // Its fields: the link, the second word, the map, the values, the
        // code bloblet and the closure; said in the map word, for a flush.
        let fields = values as u64 + 5;
        // Its region: the header, those fields, then the raw slots.
        let size = frame.map(|m| (32 + 8 * (m as u32 + 2)).div_ceil(16) * 16);
        let self_slot = frame.map(|_| 24 + 8 * values);
        let clo_slot = frame.map(|_| 24 + 8 * (values + 1));
        // A mask of register code's slots as one of the frame's values.
        let value_mask = |mask: u64| (0..raw.len()).filter(|&k| k < 64 && mask & (1 << k) != 0).filter_map(|k| value_index[k]).fold(0u64, |m, v| m | 1 << v);
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
        // The polls' ways out at a time slice's end (`emit_poll`).
        let mut polls: Vec<NPoll> = Vec::new();
        // Each call of what may not be native code branches, when it is
        // not, to a stub of its own (with where to come back to, how many
        // arguments, and whether a tail call), which calls the common
        // routine that calls out for it.
        let mut foreign: Vec<(Label, Label, usize, bool)> = Vec::new();
        // Each frame's entry past the stack cache's limit: its stub, and
        // where it comes back to.
        let mut overflows: Vec<(Label, Label, Vec<Reg>)> = Vec::new();
        // Each call of a global bound when compiled whose cell holds
        // something else when the code runs: out of the way, the call
        // through the cell (with the call's stub, and where to come back).
        let mut cell_slows: Vec<(Label, Label, Label, Vec<Reg>)> = Vec::new();
        // Where a call-out that does not return goes on (an abort), if one
        // does here.
        let (resume_at, mut uses_resume) = (a.label(), false);
        let trap = |a: &mut Asm, stubs: &mut Vec<(Label, u32)>, code: u32, c: Cond| {
            let l = a.label();
            stubs.push((l, code));
            a.to(l, Fix::If(c));
        };
        a.bind(entry);
        let entry_checked = a.label();
        for r in (1..=8).filter(|&r| reps::raw_param(params, r)) {
            unbox_f64(&mut a, r as Reg);
        }
        a.bind(entry_checked);
        if calls || frame.is_some() {
            // The arguments live (all, for a variadic procedure, whose
            // count is in X9, which the poll keeps too), raw or not.
            let n = if op_at(starts[0]) == "args" { (cells[starts[0] + 1].as_fixnum() as usize).min(8) } else { 8 };
            let (raws, values): (Vec<Reg>, Vec<Reg>) = (1..=n).map(|r| r as Reg).partition(|&r| reps::raw_param(params, r as usize));
            let (out, back) = (a.label(), a.label());
            a.e(subs_imm(FUEL, FUEL, 1));
            a.to(out, Fix::If(Cond::Lo));
            a.bind(back);
            polls.push(NPoll { out, back, values, raws, clo: captures, map: None });
        }
        let sets_first = |j: usize| matches!(op_at(j), "const" | "reg" | "stack" | "global" | "lexical");
        let ignores = |j: usize| sets_first(j) || matches!(op_at(j), "invokeself");
        let joinable = |si: usize| starts.get(si + 1).copied().filter(|&j| !target[j]);
        // Where `i64` and `u64` values are raw (`reps`): the registers as
        // each instruction starts, and ends; the ways into an instruction
        // that must unbox some first, each a stub of its own.
        let raw_refs = reps::raw_refs(&cells, &starts, &prim_name, &raw);
        let si_at: HashMap<usize, usize> = starts.iter().enumerate().map(|(si, &i)| (i, si)).collect();
        // A procedure with `int` operations gets a fixnum version first, where
        // a value tested once stays known (`reps`, `Rep::Fix`), and whose
        // tests and overflows go over to the general version, at the same
        // instruction: the registers and frame are the same in both there.
        let has_int = starts.iter().any(|&i| matches!(op_at(i), "op2" | "op2imm") && reps::int_routine(cells[i + 1].as_fixnum() as usize));
        let live = reps::live_in(&cells, &starts, &prim_name, &raw);
        let labels_g = labels;
        let labels_f: Vec<Label> = (0..=cells.len()).map(|_| a.label()).collect();
        let versions: &[bool] = if has_int { &[true, false] } else { &[false] };
        let mut edge_stubs: Vec<(Label, Vec<(usize, Rep)>, Vec<usize>, Label, Label)> = Vec::new();
        let mut int_slows: Vec<IntSlow> = Vec::new();
        for &fast in versions {
        let labels = if fast { &labels_f } else { &labels_g };
        let (reps_in, reps_out) = reps::reps_of(&cells, &starts, &prim_name, fast, &raw, params, &callees);
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
                let calls = reps::Calls { own: params, callee: callees[si - 1] };
                let first = reps::step(op, &o, &prim_name, raw_refs[si - 1], fast, &raw, calls, &mut reps);
                // `RESULT`, where a `reg` just before left it in its register
                // (`src`), is tested there.
                convert(&mut a, self.callouts, &first, labels_g[i], src);
            }
            if target[i] {
                map_stored = None;
            }
            // Before what may collect, in a frame: the slots live after it,
            // the code bloblet's, and the closure's if the code reads it.
            if frame.is_some()
                && framed[i]
                && (matches!(op, "prim" | "cellular" | "lambda" | "invokeself") || op == "invoke")
            {
                let v = values;
                let map = if unmapped { u64::MAX } else { value_mask(live_out[si - 1]) | 1 << v | if captures { 1 << (v + 1) } else { 0 } | fields << MAP_BITS };
                if map_stored != Some(map) {
                    a.es(&mov_imm64(X16, Value::fixnum(if unmapped { -(fields as i64) } else { map as i64 }).raw()));
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
                    push_frame(&mut a, LINK, size as u64);
                    // Past the stack cache's limit: the rest flushed into
                    // the heap, and this frame moved to the cache's top
                    // (`common_overflow`).
                    a.e(cmp_sp(LIMIT));
                    let (over, back) = (a.label(), a.label());
                    a.to(over, Fix::If(Cond::Lo));
                    a.bind(back);
                    let raws = (1..=8).filter(|&r| reps_in[si - 1][r] == Rep::F64).map(|r| r as Reg).collect();
                    overflows.push((over, back, raws));
                    map_stored = None;
                    if unmapped {
                        for off in (24..size as u32 - 8).step_by(8) {
                            a.e(str(XZR, FRAME, off));
                        }
                    } else {
                        let unwritten = live_out[si - 1];
                        for k in (0..raw.len()).filter(|&k| k < 64 && unwritten & (1 << k) != 0 && !raw[k]) {
                            a.e(str(XZR, FRAME, slot_off[k]));
                        }
                    }
                    ldr_field(&mut a, X9, 1);
                    a.e(str(X9, FRAME, self_slot.expect("a frame")));
                    if captures {
                        a.e(str(CLO, FRAME, clo_slot.expect("a frame")));
                    }
                }
                "pop" => {
                    pop_frame(&mut a, size.expect("a frame") as u64);
                }
                "stack" => a.e(ldr(RESULT, FRAME, slot_off[k(o(0))])),
                "setstk" => a.e(str(RESULT, FRAME, slot_off[k(o(0))])),
                "load" => a.e(ldr(reg(o(0)), FRAME, slot_off[k(o(1))])),
                "store" => {
                    a.e(str(reg(o(0)), FRAME, slot_off[k(o(1))]));
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
                // A field past `ldur`'s reach (a module of more than 31
                // members, say) through its address, in X16, as far as one
                // `sub` reaches.
                "field" => {
                    let off = field_off(k(o(0)));
                    if off < -4095 {
                        return decline("a field too far".into());
                    }
                    if off < -256 {
                        a.e(sub_imm(X16, RESULT, off.unsigned_abs() as u32));
                        a.e(ldur(RESULT, X16, 0));
                    } else {
                        a.e(ldur(RESULT, RESULT, off));
                    }
                }
                "setfield" => {
                    let off = field_off(k(o(0)));
                    if off < -4095 {
                        return decline("a field too far".into());
                    }
                    if off < -256 {
                        a.e(sub_imm(X16, RESULT, off.unsigned_abs() as u32));
                        a.e(stur(reg(o(1)), X16, 0));
                    } else {
                        a.e(stur(reg(o(1)), RESULT, off));
                    }
                    a.es(&card_mark(RESULT, off, ST, st_off(offset_of!(DState, cards)), X16, X17));
                }
                // Control, on the native stack (`docs/research/
                // native-conventions.md`, step 5). A prompt, and a mark, is a
                // frame of its own around the thunk's call, which the frames'
                // walk finds; the rest are call-outs, which walk the frames,
                // and take and put back runs of them.
                "cellular" if matches!(ROUTINES.get(k(o(0))).map(|r| r.0), Some("prompt" | "withmark" | "withmark-tail" | "abort" | "callcc" | "callcomp" | "ncallcc" | "ncallcomp" | "callone" | "ncallone" | "firstmark" | "currentmarks" | "marksof")) => {
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
                        push_frame(a, second, CONTROL_FRAME);
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
                        a.e(ldr(FRAME, SP, 8));
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
                            a.e(ldr(CLO, SP, 40));
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
                            a.e(ldr(X16, SP, 32));
                            a.e(cmp(X16, 1));
                            a.to(push, Fix::If(Cond::Ne));
                            a.e(str(2, SP, 40));
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
                        // it is taken, and `f` called with it; native here,
                        // so `ncallcc`'s too.
                        r @ ("callcc" | "callcomp" | "ncallcc" | "ncallcomp" | "callone" | "ncallone") => {
                            let after = a.label();
                            a.to(after, Fix::Adr(X9));
                            a.e(str(X9, ST, st_off(offset_of!(DState, ret_pc))));
                            let q = self.resume_proc();
                            let f = self.field(p, Field::Code(q));
                            ldr_field(&mut a, X9, f);
                            a.e(str(X9, ST, st_off(offset_of!(DState, aux))));
                            callout(&mut a, &mut stubs, self.callouts, Callout::Capture { whole: r.ends_with("callcc"), once: r.ends_with("callone") });
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
                    // What an `nclosure` made: here, the closure itself,
                    // native (register code's `lambda`), with no adapter.
                    if name == "%fx26-adapted" {
                        continue;
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
                    // An element returned: an `f64`'s bits returned raw,
                    // where the caller takes them so (`raw_return`); any
                    // other, or a read that fails, as below.
                    if name == "%fx26-flatarray-ref" && starts.get(si).is_some_and(|&j| op_at(j) == "return") {
                        let y = if op == "prim2" { reg(o(1)) } else {
                            a.es(&mov_imm64(X17, o(1).raw()));
                            X17
                        };
                        let generic = a.label();
                        flat_element(&mut a, RESULT, y, generic);
                        a.e(cmp_imm(X16, (fixpt_heap::layout::FLAT_F64 << 3) as u32));
                        a.to(generic, Fix::If(Cond::Ne));
                        a.e(ldr_x8(RESULT, X15, X14));
                        raw_return(&mut a, self.callouts);
                        a.bind(generic);
                    }
                    // A blobref's read of a scalar the layout of which is
                    // the constant: in line, as that scalar is kept.
                    // An `f64` only `f64` operations use: its bits.
                    if name == "%fx26-suffix-ref-get" && op == "prim2imm" && o(1).is_fixnum() {
                        let raw = raw_refs[si - 1];
                        let (slow, done) = (a.label(), a.label());
                        suffix_get(&mut a, o(1).as_fixnum(), raw, slow);
                        a.to(done, Fix::B);
                        a.bind(slow);
                        a.es(&mov_imm64(X17, o(1).raw()));
                        pure_call(&mut a, self.callouts, Callout::Pure { p: pn, n: 2 }, &[RESULT, X17], RESULT);
                        a.e(ldr(X9, ST, st_off(offset_of!(DState, trap))));
                        a.e(cmp_imm(X9, 0));
                        trap(&mut a, &mut stubs, PRIM_FAILED, Cond::Ne);
                        if raw {
                            unbox_f64(&mut a, RESULT);
                        }
                        a.bind(done);
                        continue;
                    }
                    // A blobref stepped a constant number of bytes along
                    // (an `extract`'s, a flat sum's variant), or a flat
                    // sum's numeric tag: in line, checked as the primitive
                    // checks.
                    let step = name == "%suffix-ref+" && o(1).is_fixnum() && (0..1 << 24).contains(&o(1).as_fixnum());
                    let tag = name == "%fx26-flat-tag" && o(1).is_fixnum();
                    let at = name == "%suffix-ref" && o(1).is_fixnum() && (0..1 << 26).contains(&o(1).as_fixnum());
                    let fits = name == "%fx26-suffix-fits" && o(1).is_fixnum() && (0..1 << 24).contains(&o(1).as_fixnum());
                    let length = name == "%fx26-suffix-ref-length" && o(1).is_fixnum() && fixpt_heap::layout::array_operand_parts(o(1).as_fixnum()).1 > 0;
                    if op == "prim2imm" && (step || tag || at || fits || length) {
                        let (slow, done) = (a.label(), a.label());
                        if step {
                            suffix_step(&mut a, o(1).as_fixnum(), slow);
                        } else if tag {
                            flat_tag(&mut a, o(1).as_fixnum(), slow);
                        } else if fits {
                            suffix_fits(&mut a, o(1).as_fixnum(), slow);
                        } else if length {
                            suffix_length(&mut a, o(1).as_fixnum(), slow);
                        } else {
                            blobref_at(&mut a, o(1).as_fixnum(), slow);
                        }
                        a.to(done, Fix::B);
                        a.bind(slow);
                        a.es(&mov_imm64(X17, o(1).raw()));
                        pure_call(&mut a, self.callouts, Callout::Pure { p: pn, n: 2 }, &[RESULT, X17], RESULT);
                        a.e(ldr(X9, ST, st_off(offset_of!(DState, trap))));
                        a.e(cmp_imm(X9, 0));
                        trap(&mut a, &mut stubs, PRIM_FAILED, Cond::Ne);
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
                        // A shift's count is an `int`, a bignum maybe: its
                        // low bits (`unbox_reg`), as a fixnum's are, in a
                        // copy (kayak's report: a bignum's pointer's bits
                        // were taken for them).
                        let count = matches!(what, "-shl" | "-shr");
                        let count_of = |a: &mut Asm, callouts: &mut Vec<Callout>| {
                            unbox_reg(a, callouts, X17);
                            a.e(lsl_imm(X17, X17, 3));
                        };
                        let y = match op {
                            "prim2" if count => {
                                a.e(mov(X17, reg(o(1))));
                                count_of(&mut a, self.callouts);
                                X17
                            }
                            "prim2" => reg(o(1)),
                            "prim2imm" => {
                                let v = o(1);
                                if v.is_fixnum() && !count {
                                    a.es(&mov_imm64(X17, v.as_fixnum() as u64));
                                } else if v.is_fixnum() || v.raw() & 7 == 3 {
                                    a.es(&mov_imm64(X17, v.raw()));
                                } else {
                                    let f = self.field(p, Field::Const(v));
                                    ldr_field(&mut a, X17, f);
                                    if count {
                                        count_of(&mut a, self.callouts);
                                    } else {
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
                // Of three, `RESULT`, a constant and `REGk`, one that never
                // collects: a blobref's element, write or variant in line,
                // where its fast path can; else a call-out with no
                // collection, the registers kept around it.
                "prim3imm" => {
                    let pn = k(o(0));
                    let name = fixpt_runtime::PRIMITIVES.get(pn).map_or("?", |d| d.name);
                    if !fixpt_runtime::never_collects(name) {
                        return decline(format!("`{op}` of `{name}`, which may collect"));
                    }
                    let (x, z) = (o(1), reg(o(2)));
                    let raw = reps::is_f64_set(&o, &prim_name) && reps_in[si - 1][k(o(2))] == Rep::F64;
                    let (slow, done) = (a.label(), a.label());
                    let code = x.is_fixnum().then(|| x.as_fixnum());
                    match (name, code) {
                        ("%fx26-blobref-index", Some(c)) => blobref_index(&mut a, c, z, slow),
                        ("%fx26-suffix-ref-set!", Some(c)) => suffix_store(&mut a, c, z, raw, slow),
                        ("%fx26-flat-variant!", Some(c)) => flat_variant(&mut a, c, z, slow),
                        _ => {}
                    }
                    if a.used(slow) {
                        a.to(done, Fix::B);
                    }
                    a.bind(slow);
                    // A raw `f64` boxed for the primitive in a copy: `REGk`
                    // stays raw for what follows.
                    let z = if raw {
                        a.e(mov(X12, z));
                        box_f64(&mut a, self.callouts, X12);
                        X12
                    } else {
                        z
                    };
                    if x.is_fixnum() || x.raw() & 7 == 3 {
                        a.es(&mov_imm64(X17, x.raw()));
                    } else {
                        let f = self.field(p, Field::Const(x));
                        ldr_field(&mut a, X17, f);
                    }
                    pure_call(&mut a, self.callouts, Callout::Pure { p: pn, n: 3 }, &[RESULT, X17, z], RESULT);
                    a.e(ldr(X9, ST, st_off(offset_of!(DState, trap))));
                    a.e(cmp_imm(X9, 0));
                    trap(&mut a, &mut stubs, PRIM_FAILED, Cond::Ne);
                    a.bind(done);
                }
                // A call-out: to Rust, on Rust's stack, which may collect;
                // everything live is in the frame by then (register code
                // sees to it), and the arguments go through the state.
                "prim" | "cellular" | "lambda" => {
                    // A closure's code: this bloblet's field.
                    let mut code_field = None;
                    // A `lambda`'s operand is its code word, no routine's number.
                    let routine = if op == "lambda" { None } else { ROUTINES.get(k(o(0))).map(|r| r.0) };
                    let c = match (op, routine) {
                        ("lambda", _) => {
                            let q = self.proc_of(o(0)).map_err(|e| format!("`{name}` makes a closure of {e}"))?;
                            code_field = Some(self.field(p, Field::Code(q)));
                            Callout::Closure { n: k(o(1)) }
                        }
                        ("cellular", Some("cons")) if k(o(1)) == 2 => Callout::Cons,
                        ("cellular", Some("rest")) if k(o(1)) == 0 => Callout::Rest,
                        ("cellular", Some("field@")) if k(o(1)) == 2 => Callout::FieldRef,
                        ("prim", _) => match fixpt_runtime::PRIMITIVES.get(k(o(0))) {
                            // `%region-nclosure`'s, natively: the same.
                            Some(d) if matches!(d.name, "%region-closure" | "%region-nclosure") => Callout::RegionClosure { n: k(o(1)) },
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
                    if let Callout::Prim { p, n: 3 } = c
                        && fixpt_runtime::PRIMITIVES[p].name == "%fx26-bytevector-u8-set!"
                    {
                        bytes_set(&mut a, slow, done);
                    }
                    if let Callout::Prim { p, n: 3 } = c
                        && fixpt_runtime::PRIMITIVES[p].name == "%fx26-suffix-ref-set!"
                    {
                        suffix_set(&mut a, slow, done);
                    }
                    if let Callout::Prim { p, n: 3 } = c
                        && fixpt_runtime::PRIMITIVES[p].name == "%fx26-suffix-ref-index"
                    {
                        suffix_index(&mut a, slow);
                        a.to(done, Fix::B);
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
                        let h = fixpt_heap::value::make_header(const { fixpt_heap::layout::kind("bloblet") }, total, 0);
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
                    // A sum or product (`%make-frozen`, `x1` its kind, else the
                    // call-out), from the free space likewise:
                    // its header, frozen fields and suffix; its fields from
                    // `x2`…; its trailer (`Heap::make_frozen`'s layout).
                    if let Callout::Prim { p, n } = c
                        && fixpt_runtime::PRIMITIVES[p].name == "%make-frozen"
                        && (2..=fixpt_heap::layout::regcode::REGS).contains(&n)
                    {
                        use fixpt_heap::layout::{H_FIELDS_FROZEN, H_SUFFIX_FROZEN, kind};
                        let total = n;
                        let (sum_k, product_k) = (const { kind("sum") }, const { kind("product") });
                        let header = |k: u8| H_SUFFIX_FROZEN.put(H_FIELDS_FROZEN.put(fixpt_heap::value::make_header(k, total, 0), 1), 1);
                        let (sum, kinded) = (a.label(), a.label());
                        a.es(&mov_imm64(X15, Value::fixnum(sum_k as i64).raw()));
                        a.e(cmp(1, X15));
                        a.to(sum, Fix::If(Cond::Eq));
                        a.es(&mov_imm64(X15, Value::fixnum(product_k as i64).raw()));
                        a.e(cmp(1, X15));
                        a.to(slow, Fix::If(Cond::Ne));
                        a.es(&mov_imm64(X17, header(product_k)));
                        a.to(kinded, Fix::B);
                        a.bind(sum);
                        a.es(&mov_imm64(X17, header(sum_k)));
                        a.bind(kinded);
                        a.e(ldr(X13, ST, st_off(offset_of!(DState, top))));
                        a.e(ldr(X14, X13, 0));
                        a.e(ldr(X15, ST, st_off(offset_of!(DState, alloc_limit))));
                        a.e(add_imm(X16, X14, 1 + total as u32));
                        a.e(cmp(X16, X15));
                        a.to(slow, Fix::If(Cond::Hi));
                        a.e(ldr(X9, ST, st_off(offset_of!(DState, words))));
                        a.e(add_lsl(X11, X9, X14, 3));
                        a.e(str(X16, X13, 0));
                        a.e(str(X17, X11, 0));
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
                        let header = fixpt_heap::value::make_header(const { fixpt_heap::layout::kind("native-closure") }, total, 0);
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
                            push_frame(&mut a, LINK, STUB_FRAME);
                        }
                        ldr_field(&mut a, X17, f);
                        a.e(movz(X9, n as u32, 0));
                        a.e(ldr(X16, ST, st_off(offset_of!(DState, closure))));
                        a.e(blr(X16));
                        if leaf_closure {
                            pop_frame(&mut a, STUB_FRAME);
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
                    // A procedure known here that takes some arguments raw:
                    // given them so, entered past its unboxing of them.
                    let callee = callees[si - 1];
                    let raws: Vec<Reg> = (1..=8).filter(|&r| reps::raw_param(callee, r)).map(|r| r as Reg).collect();
                    let (stub, after) = (a.label(), a.label());
                    // The callee's convention, by its type (`regcode::CONVS`):
                    // native, its code called with no look; cellular, called
                    // out (`common_foreign`) with none; fx, looked at, its
                    // code in the code area or not (`code_lo`).
                    use fixpt_heap::layout::regcode::conv;
                    let cv = k(o(1));
                    let not_native = |a: &mut Asm| {
                        if cv == conv("cellular") {
                            a.to(stub, Fix::B);
                            return;
                        }
                        a.e(ldur(X16, CLO, field_off(CLOSURE_WORD)));
                        if cv == conv("fx") {
                            a.e(ldr(X17, ST, st_off(offset_of!(DState, code_lo))));
                            a.e(cmp(X16, X17));
                            a.to(stub, Fix::If(Cond::Lo));
                        }
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
                                if !raws.is_empty() {
                                    a.e(add_imm(X16, X16, raw_entry_skip(raws.len())));
                                }
                            }
                            // Another compile's native code (`native_params`),
                            // what the cell holds while the guard holds:
                            // entered past its unboxing of what it takes raw.
                            Some(Field::Const(_)) => {
                                a.e(ldur(X16, CLO, field_off(CLOSURE_WORD)));
                                if !raws.is_empty() {
                                    a.e(add_imm(X16, X16, raw_entry_skip(raws.len())));
                                }
                            }
                            Some(g) => {
                                let f = self.field(p, g);
                                ldr_field(&mut a, CLO, f);
                                a.e(ldur(X16, CLO, field_off(CLOSURE_WORD)));
                            }
                            None => unreachable!("a global bound is called"),
                        }
                        a.bind(join);
                        cell_slows.push((slow, join, stub, raws));
                        foreign.push((stub, after, k(o(0)), tail));
                    } else {
                        match pending.take() {
                            Some(Field::Code(q)) => {
                                let f = self.field(p, Field::Code(q));
                                ldr_field(&mut a, X16, f);
                                if !raws.is_empty() {
                                    a.e(add_imm(X16, X16, raw_entry_skip(raws.len())));
                                }
                            }
                            // Through the global's cell, when the code runs: what
                            // it holds then, native code or not.
                            Some(Field::Cell(c)) => {
                                let f = self.field(p, Field::Cell(c));
                                ldr_field(&mut a, X9, f);
                                a.e(ldur(CLO, X9, field_off(2)));
                                not_native(&mut a);
                                if cv != conv("native") {
                                    foreign.push((stub, after, k(o(0)), tail));
                                }
                            }
                            Some(g) => {
                                let f = self.field(p, g);
                                ldr_field(&mut a, CLO, f);
                                a.e(ldur(X16, CLO, field_off(CLOSURE_WORD)));
                            }
                            None => {
                                a.e(mov(CLO, RESULT));
                                not_native(&mut a);
                                if cv != conv("native") {
                                    foreign.push((stub, after, k(o(0)), tail));
                                }
                            }
                        }
                    }
                    // The count, for a variadic callee (`vargs`), Larceny's
                    // way: every call passes it.
                    a.e(movz(X9, k(o(0)) as u32, 0));
                    a.e(add(X16, X16, DELTA));
                    a.e(if tail { br(X16) } else { blr(X16) });
                    a.bind(after);
                    if !tail && raw_refs[si - 1] {
                        take_raw_f64(&mut a);
                    }
                }
                "invokeself" => {
                    if let Some(s) = clo_slot.filter(|_| captures) {
                        a.e(ldr(CLO, FRAME, s));
                    }
                    a.to(entry_checked, Fix::Bl);
                    if raw_refs[si - 1] {
                        take_raw_f64(&mut a);
                    }
                }
                "return" if reps_in[si - 1][0] == Rep::F64 => raw_return(&mut a, self.callouts),
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
                            // What the loop's head reads, kept as it is
                            // here, raw or not; the frame's map for here.
                            let t = si_at[&to];
                            let rep = reps_in[si - 1];
                            let kept = |r: usize| live[t][r] && !matches!(rep[r], Rep::Undefined);
                            let raw_r = |r: usize| matches!(rep[r], Rep::F64 | Rep::Raw { .. });
                            let vals: Vec<Reg> = (0..=8).filter(|&r| kept(r) && !raw_r(r)).map(|r| r as Reg).collect();
                            let raws: Vec<Reg> = (0..=8).filter(|&r| kept(r) && raw_r(r)).map(|r| r as Reg).collect();
                            let map = (frame.is_some() && framed[i]).then(|| {
                                let v = values;
                                if unmapped {
                                    -(fields as i64)
                                } else {
                                    (value_mask(live_out[si - 1]) | 1 << v | if captures { 1 << (v + 1) } else { 0 } | fields << MAP_BITS) as i64
                                }
                            });
                            let (out, back) = (a.label(), a.label());
                            a.e(subs_imm(FUEL, FUEL, 1));
                            a.to(out, Fix::If(Cond::Lo));
                            a.bind(back);
                            polls.push(NPoll { out, back, values: vals, raws, clo: captures && !framed[i], map });
                            map_stored = None;
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
        for (slow, join, stub, raws) in &cell_slows {
            a.bind(*slow);
            // Not the procedure known: what it holds takes values.
            for &r in raws {
                box_f64(&mut a, self.callouts, r);
            }
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
        for (over, back, raws) in &overflows {
            a.bind(*over);
            // The arguments it keeps are values: those raw boxed around it.
            for &r in raws {
                box_f64(&mut a, self.callouts, r);
            }
            // Through the link, which the frame holds already: X9 may be a
            // variadic procedure's count.
            ldr_field(&mut a, X16, 1);
            a.es(&mov_imm64(X17, info));
            a.e(ldr(LINK, ST, st_off(offset_of!(DState, overflow))));
            a.e(blr(LINK));
            for &r in raws {
                unbox_f64(&mut a, r);
            }
            a.to(*back, Fix::B);
        }
        // The traps, out of the way: a stub per site, calling its kind's
        // stub, which goes to the machine's common trap (`common_trap`),
        // which records the trap and where, and leaves.
        for poll in std::mem::take(&mut polls) {
            emit_poll(&mut a, &poll, &mut stubs);
        }
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
        self.procs[p].code = crate::arm64::bytes(&a.finish()?);
        self.procs[p].len = 4 * own;
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

/// The word a call that takes an `f64` value raw puts where the callee
/// returns to: `movk xzr, #0xf64f, lsl #48`, which does nothing, and which
/// nothing else emits (`TODO.md` §91).
fn raw_f64_mark() -> u32 {
    movk(XZR, 0xf64f, 3)
}

/// After a call whose value only `f64` operations use: the value raw in
/// `RESULT`. A callee returning an `f64` raw sees the mark at its return
/// address and returns 8 past it (`raw_return`); any other return (a
/// callee's that does not know, a stub's, an underflow's, a continuation's)
/// comes to the mark, which does nothing, and the value is unboxed.
fn take_raw_f64(a: &mut Asm) {
    let (boxed, join) = (a.label(), a.label());
    a.e(raw_f64_mark());
    a.to(boxed, Fix::B);
    a.to(join, Fix::B);
    a.bind(boxed);
    unbox_f64(a, RESULT);
    a.bind(join);
}

/// A return of the raw `f64` in `RESULT`: as it is, 8 past the return
/// address, where the caller takes it so (its mark there, `take_raw_f64`);
/// else boxed, to the return address.
fn raw_return(a: &mut Asm, callouts: &mut Vec<Callout>) {
    let boxed = a.label();
    a.e(ldur_w(X16, LINK, 0));
    a.es(&mov_imm64(X17, raw_f64_mark() as u64));
    a.e(cmp(X16, X17));
    a.to(boxed, Fix::If(Cond::Ne));
    a.e(add_imm(LINK, LINK, 8));
    a.e(ret());
    a.bind(boxed);
    box_f64(a, callouts, RESULT);
    a.e(ret());
}

/// Bytes from a procedure's entry past its unboxing of the `n` parameters
/// it takes raw: where a call that knows it, passing them raw, enters.
fn raw_entry_skip(n: usize) -> u32 {
    let mut a = Asm::new();
    unbox_f64(&mut a, 1);
    // A word after it, where its last label is placed.
    a.e(ret());
    (4 * (a.finish().expect("placed").len() - 1) * n) as u32
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
    box_bits(a, slow);
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

/// An `f64` boxed from the free space into `RESULT`, its bits in X9; to
/// `slow` when there is no room. Uses X11 and X13 to X17.
fn box_bits(a: &mut Asm, slow: Label) {
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
}

/// Suffix ref `r` (tag `010`, `docs/object-model.md`) taken apart, to `slow`
/// unless it is one whose owner has a trailer and a header of one word:
/// X15 its offset, X11 where its owner's suffix starts, X12 the owner's
/// header, X13 the suffix's length `B`, X16 the trailer's distance (the
/// last field's index: field `k`, 2 ≤ k ≤ X16, is `8k` bytes before X11). The owner is the heap's word
/// `ubfx` bits 3..37 of the ref, the offset bits 37.. (`lsr #37`). Uses X9,
/// X14 and X16 too.
fn suffix_owner(a: &mut Asm, r: Reg, slow: Label) {
    use fixpt_heap::layout::*;
    use fixpt_heap::value::{SUFFIX_OFFSET_SHIFT, SUFFIX_OWNER_BITS, TAG_SUFFIX_REF, TAG_TRAILER};
    a.e(and_low(X16, r, 3));
    a.e(cmp_imm(X16, TAG_SUFFIX_REF as u32));
    a.to(slow, Fix::If(Cond::Ne));
    a.e(ubfx(X14, r, 3, SUFFIX_OWNER_BITS));
    a.e(lsr_imm(X15, r, SUFFIX_OFFSET_SHIFT));
    a.e(ldr(X9, ST, st_off(offset_of!(DState, words))));
    a.e(add_lsl(X11, X9, X14, 3));
    // The trailer, the last field, says how far back the header is.
    a.e(ldur(X16, X11, -8));
    a.e(and_low(X9, X16, 3));
    a.e(cmp_imm(X9, TAG_TRAILER as u32));
    a.to(slow, Fix::If(Cond::Ne));
    a.e(ubfx(X16, X16, T_DISTANCE.lo, 32));
    a.e(lsl_imm(X9, X16, 3));
    a.e(sub(X9, X11, X9));
    a.e(ldur(X12, X9, -8));
    a.e(ubfx(X9, X12, H_LARGE.lo, 1));
    a.e(cmp_imm(X9, 0));
    a.to(slow, Fix::If(Cond::Ne));
    a.e(lsr_imm(X13, X12, H_BYTES.lo));
}

/// Suffix ref `r` taken apart as `suffix_owner` does, to `slow` unless
/// its owner is a program's own bloblet or a flat array whose suffix is
/// not frozen.
fn suffix_writable(a: &mut Asm, r: Reg, slow: Label) {
    use fixpt_heap::layout::*;
    suffix_owner(a, r, slow);
    let owned = a.label();
    a.e(ubfx(X9, X12, H_KIND.lo, H_KIND.width));
    a.e(cmp_imm(X9, const { kind("bloblet") } as u32));
    a.to(owned, Fix::If(Cond::Eq));
    a.e(cmp_imm(X9, const { kind("flat-array") } as u32));
    a.to(slow, Fix::If(Cond::Ne));
    a.bind(owned);
    a.e(ubfx(X9, X12, H_SUFFIX_FROZEN.lo, 1));
    a.e(cmp_imm(X9, 0));
    a.to(slow, Fix::If(Cond::Ne));
}

/// `blobref-set!` (`%fx26-suffix-ref-set!`) of the suffix ref in `RESULT`,
/// a scalar of layout `code`, to `v` (with `raw`, an `f64`'s bits): unit
/// into `RESULT`; to `slow` as `suffix_set` goes.
fn suffix_store(a: &mut Asm, code: i64, v: Reg, raw: bool, slow: Label) {
    use fixpt_heap::layout::*;
    suffix_writable(a, RESULT, slow);
    a.e(add_imm(X9, X15, flat_size(code) as u32));
    a.e(cmp(X9, X13));
    a.to(slow, Fix::If(Cond::Hi));
    a.e(add(X11, X11, X15));
    match code {
        FLAT_F64 if raw => a.e(stur(v, X11, 0)),
        FLAT_F64 => {
            a.e(ldur(X13, v, -(fixpt_heap::value::TAG_BLOBLET as i64)));
            a.e(stur(X13, X11, 0));
        }
        FLAT_F32 => {
            a.e(lsr_imm(X13, v, 32));
            a.e(stur_w(X13, X11, 0));
        }
        FLAT_I64 | FLAT_U64 => {
            a.e(tst_low(v, 3));
            a.to(slow, Fix::If(Cond::Ne));
            a.e(asr_imm(X13, v, 3));
            a.e(stur(X13, X11, 0));
        }
        _ => {
            a.e(asr_imm(X13, v, 3));
            a.e(stur_w(X13, X11, 0));
        }
    }
    a.es(&mov_imm64(RESULT, Value::UNIT.raw()));
}

/// `blobref-index` (`%fx26-blobref-index`) of the suffix ref in `RESULT`
/// at `i`, of layout `code` (`layout::array_operand`), into `RESULT`; to `slow`
/// unless `i` is a fixnum below `n` and the element within the suffix.
fn blobref_index(a: &mut Asm, code: i64, i: Reg, slow: Label) {
    use fixpt_heap::value::SUFFIX_OFFSET_SHIFT;
    let (n, size) = fixpt_heap::layout::array_operand_parts(code);
    a.e(tst_low(i, 3));
    a.to(slow, Fix::If(Cond::Ne));
    suffix_owner(a, RESULT, slow);
    a.e(asr_imm(X9, i, 3));
    a.es(&mov_imm64(X17, n as u64));
    a.e(cmp(X9, X17));
    a.to(slow, Fix::If(Cond::Hs));
    if size > 0 && size & (size - 1) == 0 {
        a.e(lsl_imm(X9, X9, size.trailing_zeros()));
    } else {
        a.es(&mov_imm64(X17, size as u64));
        a.e(mul(X9, X9, X17));
    }
    a.e(add(X16, X15, X9));
    a.e(cmp(X16, X13));
    a.to(slow, Fix::If(Cond::Hs));
    a.e(lsl_imm(X9, X9, SUFFIX_OFFSET_SHIFT));
    a.e(add(RESULT, RESULT, X9));
}

/// `blobref-variant!` (`%fx26-flat-variant!`) of the suffix ref in `RESULT`
/// to label `l`, of layout `code`: the tag's `code & 7` bytes written (with
/// a numeric key, the label; else the index of the first of the owner's
/// fields that holds it, by identity, as the primitive looks), and a ref
/// to the variant, `code >> 8` along, into `RESULT`; to `slow` unless the
/// tag fits and the variant is within a suffix that may be written.
fn flat_variant(a: &mut Asm, code: i64, l: Reg, slow: Label) {
    use fixpt_heap::value::SUFFIX_OFFSET_SHIFT;
    let (w, p) = (code & 7, code >> 8);
    let numeric = code & 8 != 0;
    if numeric {
        a.e(tst_low(l, 3));
        a.to(slow, Fix::If(Cond::Ne));
        a.e(asr_imm(X17, l, 3));
    }
    suffix_writable(a, RESULT, slow);
    if !numeric {
        // Fields 2 to the trailer's distance (X16), the first that is `l`.
        let (look, found) = (a.label(), a.label());
        a.e(movz(X17, 2, 0));
        a.bind(look);
        a.e(cmp(X17, X16));
        a.to(slow, Fix::If(Cond::Hi));
        a.e(lsl_imm(X9, X17, 3));
        a.e(sub(X9, X11, X9));
        a.e(ldur(X9, X9, 0));
        a.e(cmp(X9, l));
        a.to(found, Fix::If(Cond::Eq));
        a.e(add_imm(X17, X17, 1));
        a.to(look, Fix::B);
        a.bind(found);
        a.e(sub_imm(X17, X17, 2));
    }
    if w < 8 {
        a.e(lsr_imm(X9, X17, 8 * w as u32));
        a.e(cmp_imm(X9, 0));
        a.to(slow, Fix::If(Cond::Ne));
    }
    a.es(&mov_imm64(X9, p as u64));
    a.e(add(X16, X15, X9));
    a.e(cmp(X16, X13));
    a.to(slow, Fix::If(Cond::Hs));
    a.e(add(X11, X11, X15));
    a.e(match w {
        1 => sturb(X17, X11, 0),
        2 => sturh(X17, X11, 0),
        _ => stur_w(X17, X11, 0),
    });
    a.e(lsl_imm(X9, X9, SUFFIX_OFFSET_SHIFT));
    a.e(add(RESULT, RESULT, X9));
}

/// `blobref-at` (`%suffix-ref`) of the bloblet in `RESULT` at byte `d` of
/// its suffix, into `RESULT`: the ref, its owner the suffix's start, a
/// word of the heap (`Value::suffix_ref`); to `slow` (the primitive's)
/// unless the bloblet has a trailer, a header of one word, a suffix short
/// enough for refs and a byte `d`.
fn blobref_at(a: &mut Asm, d: i64, slow: Label) {
    use fixpt_heap::layout::*;
    use fixpt_heap::value::{SUFFIX_OFFSET_LIMIT, SUFFIX_OFFSET_SHIFT, SUFFIX_OWNER_BITS, TAG_BLOBLET, TAG_SUFFIX_REF, TAG_TRAILER};
    a.e(and_low(X16, RESULT, 3));
    a.e(cmp_imm(X16, TAG_BLOBLET as u32));
    a.to(slow, Fix::If(Cond::Ne));
    a.e(sub_imm(X11, RESULT, TAG_BLOBLET as u32));
    a.e(ldur(X16, X11, -8));
    a.e(and_low(X9, X16, 3));
    a.e(cmp_imm(X9, TAG_TRAILER as u32));
    a.to(slow, Fix::If(Cond::Ne));
    a.e(ubfx(X16, X16, T_DISTANCE.lo, 32));
    a.e(lsl_imm(X9, X16, 3));
    a.e(sub(X9, X11, X9));
    a.e(ldur(X12, X9, -8));
    a.e(ubfx(X9, X12, H_LARGE.lo, 1));
    a.e(cmp_imm(X9, 0));
    a.to(slow, Fix::If(Cond::Ne));
    a.e(lsr_imm(X13, X12, H_BYTES.lo));
    a.es(&mov_imm64(X9, SUFFIX_OFFSET_LIMIT as u64));
    a.e(cmp(X13, X9));
    a.to(slow, Fix::If(Cond::Hs));
    a.es(&mov_imm64(X9, d as u64));
    a.e(cmp(X9, X13));
    a.to(slow, Fix::If(Cond::Hs));
    // The owner, the suffix's word in the heap, as `Heap::ix` counts it,
    // where it fits its bits.
    a.e(ldr(X9, ST, st_off(offset_of!(DState, words))));
    a.e(sub(X11, X11, X9));
    a.e(lsr_imm(X9, X11, 3 + SUFFIX_OWNER_BITS));
    a.e(cmp_imm(X9, 0));
    a.to(slow, Fix::If(Cond::Ne));
    a.es(&mov_imm64(X9, ((d as u64) << SUFFIX_OFFSET_SHIFT) | TAG_SUFFIX_REF));
    a.e(orr(RESULT, X11, X9));
}

/// Suffix ref `RESULT` moved `d` bytes along (`%suffix-ref+`), into
/// `RESULT`; to `slow` (the primitive's) unless it stays within its
/// owner's suffix. By none it is itself, once seen to be a suffix ref.
fn suffix_step(a: &mut Asm, d: i64, slow: Label) {
    use fixpt_heap::value::{SUFFIX_OFFSET_SHIFT, TAG_SUFFIX_REF};
    if d == 0 {
        a.e(and_low(X16, RESULT, 3));
        a.e(cmp_imm(X16, TAG_SUFFIX_REF as u32));
        a.to(slow, Fix::If(Cond::Ne));
        return;
    }
    suffix_owner(a, RESULT, slow);
    a.es(&mov_imm64(X9, d as u64));
    a.e(add(X9, X15, X9));
    a.e(cmp(X9, X13));
    a.to(slow, Fix::If(Cond::Hs));
    a.es(&mov_imm64(X9, (d as u64) << SUFFIX_OFFSET_SHIFT));
    a.e(add(RESULT, RESULT, X9));
}

/// A new blobref (`%fx26-suffix-fits`): the suffix ref in `RESULT` left
/// there, to `slow` (the primitive's, which says why) unless `size` bytes
/// from it lie in its owner's suffix.
fn suffix_fits(a: &mut Asm, size: i64, slow: Label) {
    suffix_owner(a, RESULT, slow);
    a.es(&mov_imm64(X9, size as u64));
    a.e(add(X9, X15, X9));
    a.e(cmp(X9, X13));
    a.to(slow, Fix::If(Cond::Hi));
}

/// `blobref-length` (`%fx26-suffix-ref-length`) of the suffix ref in
/// `RESULT`, of the layout `code` (`layout::array_operand`, `size` > 0), into
/// `RESULT`: `n`, or, for an array that runs to the end of the suffix
/// (`FLAT_TO_THE_END`), the whole elements left of it; to `slow` (the
/// primitive's) for what is no suffix ref, or one whose owner it does not
/// find in line.
fn suffix_length(a: &mut Asm, code: i64, slow: Label) {
    let (n, size) = fixpt_heap::layout::array_operand_parts(code);
    if n != fixpt_heap::layout::FLAT_TO_THE_END {
        a.e(and_low(X16, RESULT, 3));
        a.e(cmp_imm(X16, fixpt_heap::value::TAG_SUFFIX_REF as u32));
        a.to(slow, Fix::If(Cond::Ne));
        a.es(&mov_imm64(RESULT, Value::fixnum(n).raw()));
        return;
    }
    suffix_owner(a, RESULT, slow);
    a.e(sub(X9, X13, X15));
    a.es(&mov_imm64(X17, size as u64));
    a.e(udiv(X9, X9, X17));
    a.e(lsl_imm(RESULT, X9, 3));
}

/// `blobref-index` (`%fx26-suffix-ref-index`) of the suffix ref in `x1`,
/// at `x2`, of the layout in `x3` (`layout::array_operand`), into `RESULT`: the
/// ref `x2 × size` bytes along, within the suffix; to `slow` (the
/// call-out, which says why) unless `x2` is a fixnum below `n`.
fn suffix_index(a: &mut Asm, slow: Label) {
    use fixpt_heap::value::SUFFIX_OFFSET_SHIFT;
    a.e(tst_low(2, 3));
    a.to(slow, Fix::If(Cond::Ne));
    suffix_owner(a, 1, slow);
    a.e(asr_imm(X9, 2, 3));
    // The operand a fixnum: its length past the tag and the size.
    use fixpt_heap::layout::{ARRAY_OPERAND_LENGTH_SHIFT, ARRAY_OPERAND_SIZE_BITS};
    a.e(lsr_imm(X17, 3, 3 + ARRAY_OPERAND_LENGTH_SHIFT));
    a.e(cmp(X9, X17));
    a.to(slow, Fix::If(Cond::Hs));
    a.e(ubfx(X17, 3, 3, ARRAY_OPERAND_SIZE_BITS));
    a.e(mul(X9, X9, X17));
    // The whole element within the suffix, which is the bound of an array
    // that runs to the end of it (`FLAT_TO_THE_END`, `TODO.md` §77): one
    // only partly in it is the primitive's to judge.
    a.e(add(X16, X15, X9));
    a.e(add(X16, X16, X17));
    a.e(cmp(X16, X13));
    a.to(slow, Fix::If(Cond::Hi));
    a.e(lsl_imm(X9, X9, SUFFIX_OFFSET_SHIFT));
    a.e(add(RESULT, 1, X9));
}

/// A flat sum's tag at the suffix ref in `RESULT`, into `RESULT`, of
/// layout `code` (`%fx26-flat-tag`): with a numeric key, its `code & 7`
/// bytes, a fixnum; else its byte `b` indexes the owner's fields, and the
/// label is field `b + 2`. To `slow` for a read past the suffix, or an
/// index past the fields.
fn flat_tag(a: &mut Asm, code: i64, slow: Label) {
    let w = code & 7;
    suffix_owner(a, RESULT, slow);
    a.e(add_imm(X9, X15, w as u32));
    a.e(cmp(X9, X13));
    a.to(slow, Fix::If(Cond::Hi));
    a.e(add(X14, X11, X15));
    a.e(match w {
        1 => ldurb(X13, X14, 0),
        2 => ldurh(X13, X14, 0),
        _ => ldur_w(X13, X14, 0),
    });
    if code & 8 != 0 {
        a.e(lsl_imm(RESULT, X13, 3));
        return;
    }
    a.e(add_imm(X13, X13, 2));
    a.e(cmp(X13, X16));
    a.to(slow, Fix::If(Cond::Hi));
    a.e(lsl_imm(X13, X13, 3));
    a.e(sub(X13, X11, X13));
    a.e(ldur(RESULT, X13, 0));
}

/// `blobref-get` of the suffix ref in `RESULT`, a scalar of layout `code`
/// (`fixpt_heap::layout::FLAT_*`), into `RESULT`, at any alignment: an
/// `f64` boxed, an `f32` an immediate, a 32-bit integer its fixnum, a
/// 64-bit one its fixnum where it is one; to `slow` (the primitive's) for
/// what it does not do, or a read past the suffix. With `raw`, an `f64`'s
/// bits, not boxed.
fn suffix_get(a: &mut Asm, code: i64, raw: bool, slow: Label) {
    use fixpt_heap::layout::*;
    suffix_owner(a, RESULT, slow);
    a.e(add_imm(X9, X15, flat_size(code) as u32));
    a.e(cmp(X9, X13));
    a.to(slow, Fix::If(Cond::Hi));
    a.e(add(X11, X11, X15));
    match code {
        FLAT_F64 if raw => a.e(ldur(RESULT, X11, 0)),
        FLAT_F64 => {
            a.e(ldur(X9, X11, 0));
            box_bits(a, slow);
        }
        FLAT_F32 => {
            a.e(ldur_w(X13, X11, 0));
            a.e(lsl_imm(X13, X13, 32));
            a.e(add_imm(RESULT, X13, (Value::f32(0.0).raw() & 0xff) as u32));
        }
        FLAT_I32 => {
            a.e(ldur_w(X13, X11, 0));
            a.e(lsl_imm(X13, X13, 32));
            a.e(asr_imm(RESULT, X13, 29));
        }
        FLAT_U32 => {
            a.e(ldur_w(X13, X11, 0));
            a.e(lsl_imm(RESULT, X13, 3));
        }
        FLAT_I64 => {
            a.e(ldur(X13, X11, 0));
            a.e(lsl_imm(X14, X13, 3));
            a.e(asr_imm(X15, X14, 3));
            a.e(cmp(X15, X13));
            a.to(slow, Fix::If(Cond::Ne));
            a.e(mov(RESULT, X14));
        }
        _ => {
            a.e(ldur(X13, X11, 0));
            a.e(lsr_imm(X15, X13, 60));
            a.e(cmp_imm(X15, 0));
            a.to(slow, Fix::If(Cond::Ne));
            a.e(lsl_imm(RESULT, X13, 3));
        }
    }
}

/// `blobref-set!` of the suffix ref in `x1`, a scalar of the layout the
/// fixnum in `x2` says, to `x3`: into a program's own bloblet or a flat
/// array whose suffix is not frozen, within it; else to `slow` (the
/// call-out, which says why), as for a 64-bit integer that is a bignum.
/// Unit into `RESULT`, and to `done`.
fn suffix_set(a: &mut Asm, slow: Label, done: Label) {
    use fixpt_heap::layout::*;
    let (v, c) = (3 as Reg, 2 as Reg);
    suffix_writable(a, 1, slow);
    // The width: 8 for the 64-bit layouts, as bits of a word, else 4.
    a.e(lsr_imm(X16, c, 3));
    let wide = [FLAT_I64, FLAT_U64, FLAT_F64].iter().fold(0u32, |m, c| m | 1 << c);
    a.e(movz(X9, wide, 0));
    a.e(lsrv(X9, X9, X16));
    a.e(and_low(X9, X9, 1));
    a.e(lsl_imm(X9, X9, 2));
    a.e(add_imm(X9, X9, 4));
    a.e(add(X9, X15, X9));
    a.e(cmp(X9, X13));
    a.to(slow, Fix::If(Cond::Hi));
    a.e(add(X11, X11, X15));
    let is = |a: &mut Asm, code: i64, not: Label| {
        a.e(cmp_imm(c, (code << 3) as u32));
        a.to(not, Fix::If(Cond::Ne));
    };
    let (not_f64, not_f32, wide, stored) = (a.label(), a.label(), a.label(), a.label());
    is(a, FLAT_F64, not_f64);
    a.e(ldur(X13, v, -(fixpt_heap::value::TAG_BLOBLET as i64)));
    a.e(stur(X13, X11, 0));
    a.to(stored, Fix::B);
    a.bind(not_f64);
    is(a, FLAT_F32, not_f32);
    a.e(lsr_imm(X13, v, 32));
    a.e(stur_w(X13, X11, 0));
    a.to(stored, Fix::B);
    a.bind(not_f32);
    a.e(cmp_imm(c, (FLAT_I64 << 3) as u32));
    a.to(wide, Fix::If(Cond::Eq));
    a.e(cmp_imm(c, (FLAT_U64 << 3) as u32));
    a.to(wide, Fix::If(Cond::Eq));
    a.e(asr_imm(X13, v, 3));
    a.e(stur_w(X13, X11, 0));
    a.to(stored, Fix::B);
    a.bind(wide);
    a.e(tst_low(v, 3));
    a.to(slow, Fix::If(Cond::Ne));
    a.e(asr_imm(X13, v, 3));
    a.e(stur(X13, X11, 0));
    a.bind(stored);
    a.es(&mov_imm64(RESULT, Value::UNIT.raw()));
    a.to(done, Fix::B);
}

/// `bytevector-u8-set!` of the bytevector in `x1` at `x2` to the `u8` in
/// `x3` (`TODO.md` §84): its byte stored, no barrier for a byte; an index
/// that is no fixnum, or out of range, to `slow` (the call-out, which
/// refuses it). Unit into `RESULT`, and to `done`.
fn bytes_set(a: &mut Asm, slow: Label, done: Label) {
    let (bv, i, v) = (1 as Reg, 2 as Reg, 3 as Reg);
    a.e(tst_low(i, 3));
    a.to(slow, Fix::If(Cond::Ne));
    a.e(asr_imm(X15, i, 3));
    a.e(ldur(X14, bv, -4));
    a.e(cmp(X15, X14));
    a.to(slow, Fix::If(Cond::Hs));
    a.e(lsr_imm(X13, v, 3));
    a.e(add(X11, bv, X15));
    a.e(add_imm(X11, X11, 4));
    a.e(strb(X13, X11));
    a.es(&mov_imm64(RESULT, Value::UNIT.raw()));
    a.to(done, Fix::B);
}

/// The parameters register word `rw`'s procedure takes raw
/// (`reps::raw_params`), its slots as compiled (`register_cells`).
fn register_params(h: &Heap, rw: Value) -> u8 {
    let cells = register_cells(h, rw);
    let (mut starts, mut frame, mut i) = (Vec::new(), None, 0);
    while i < cells.len() {
        starts.push(i);
        let (op, n, _) = OPS[cells[i].as_fixnum() as usize];
        if op == "save" {
            frame = Some(cells[i + 1].as_fixnum() as usize);
        }
        i += 1 + n;
    }
    let prim_name = |p: usize| fixpt_runtime::PRIMITIVES.get(p).map_or("?", |d| d.name);
    let raw = frame.map_or(Vec::new(), |m| reps::raw_slots(&cells, &starts, &prim_name, m));
    reps::raw_params(&cells, &starts, &prim_name, &raw)
}

/// Register word `rw`'s cells, as they are compiled: a frame slot that
/// holds an `f64` and something else in turn split (`reps::split_slots`).
fn register_cells(h: &Heap, rw: Value) -> Vec<Value> {
    let cells: Vec<Value> = (WORD_CELL0..=h.bloblet_head(rw).fields).map(|k| h.bloblet_slot(rw, k)).collect();
    let prim_name = |p: usize| fixpt_runtime::PRIMITIVES.get(p).map_or("?", |d| d.name);
    reps::split_slots(cells, &prim_name)
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

/// `RESULT`, the fixnum of an integer, wrapped to the range of a type of
/// `bits` bits (8 or 32): its bits 3 to `bits` + 2 kept, sign-extended if
/// the type is signed.
fn wrap_small(a: &mut Asm, signed: bool, bits: u32) {
    if signed {
        a.e(lsl_imm(RESULT, RESULT, 61 - bits));
        a.e(asr_imm(RESULT, RESULT, 61 - bits));
    } else {
        a.e(and_bits(RESULT, RESULT, 3, bits));
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
        "char?" | "%fx26-f32?" => {
            a.e(and_low(X13, x, 8));
            let tag = if name == "char?" { Value::char('\0') } else { Value::f32(0.0) };
            a.e(cmp_imm(X13, (tag.raw() & 0xFF) as u32));
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
        "exact-integer?" => &[const { kind("bignum") }],
        "symbol?" => &[const { kind("symbol") }],
        "string?" => &[const { kind("string") }],
        "%fx26-array?" => &[const { kind("bloblet") }],
        "%fx26-box?" => &[const { kind("box") }],
        "%fx26-sum?" => &[const { kind("sum") }],
        "%fx26-product?" => &[const { kind("product") }],
        "%fx26-procedure?" => &[
            const { kind("closure") },
            const { kind("primitive") },
            const { kind("continuation") },
            const { kind("cellular-closure") },
            const { kind("native-closure") },
            const { kind("cellular-continuation") },
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
    // a remainder (`remainder`, the dividend's sign, always a fixnum) is
    // `modulo`'s when it has the divisor's sign, or is 0.
    if name == "%fx26-quotient" || name == "modulo" || name == "%fx26-remainder" {
        fixnums(a);
        nonzero(a);
        a.e(sdiv(X13, x, y));
        if name == "%fx26-quotient" {
            a.e(lsl_imm(X14, X13, 3));
            a.e(asr_imm(X15, X14, 3));
            a.e(cmp(X15, X13));
            a.to(slow, Fix::If(Cond::Ne));
        } else if name == "%fx26-remainder" {
            a.e(msub(X14, X13, y, x));
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
    // `arithmetic-shift` of fixnums: left by fewer than 61 while the result
    // stays a fixnum (shifted back, the same), right (floor) by fewer than
    // 63; a bignum, and the rest, the primitive's.
    if name == "%fx26-arithmetic-shift" {
        fixnums(a);
        let (right, done) = (a.label(), a.label());
        a.e(asr_imm(X14, y, 3));
        a.e(cmp(X14, XZR));
        a.to(right, Fix::If(Cond::Lt));
        a.e(cmp_imm(X14, 61));
        a.to(slow, Fix::If(Cond::Ge));
        a.e(lslv(X13, x, X14));
        a.e(asrv(X15, X13, X14));
        a.e(cmp(X15, x));
        a.to(slow, Fix::If(Cond::Ne));
        a.e(mov(RESULT, X13));
        a.to(done, Fix::B);
        a.bind(right);
        a.e(sub(X14, XZR, X14));
        a.e(cmp_imm(X14, 63));
        a.to(slow, Fix::If(Cond::Hs));
        a.e(asrv(X13, x, X14));
        a.e(asr_imm(X13, X13, 3));
        a.e(lsl_imm(RESULT, X13, 3));
        a.bind(done);
        return true;
    }
    // A bloblet's count of fields (`array-length`): its trailer's distance,
    // where it has a trailer (`Heap::make_bloblet`'s layout).
    if name == "%bloblet-fields" {
        a.e(and_low(X13, x, 3));
        a.e(cmp_imm(X13, fixpt_heap::value::TAG_BLOBLET as u32));
        a.to(slow, Fix::If(Cond::Ne));
        a.e(ldur(X16, x, field_off(1)));
        a.e(and_low(X13, X16, 3));
        a.e(cmp_imm(X13, fixpt_heap::value::TAG_TRAILER as u32));
        a.to(slow, Fix::If(Cond::Ne));
        a.e(ubfx(X16, X16, fixpt_heap::layout::T_DISTANCE.lo, 32));
        a.e(lsl_imm(RESULT, X16, 3));
        return true;
    }
    // A bytevector (`TODO.md` §84), all suffix: its length the word before
    // the bytes, a byte at its index. The type says it is one; an index
    // past it, or not a fixnum, is the primitive's to refuse.
    if name == "bytevector-length" {
        a.e(ldur(X13, x, -4));
        a.e(lsl_imm(RESULT, X13, 3));
        return true;
    }
    if name == "bytevector-u8-ref" {
        fixnum(a, y);
        a.e(ldur(X14, x, -4));
        a.e(asr_imm(X15, y, 3));
        a.e(cmp(X15, X14));
        a.to(slow, Fix::If(Cond::Hs));
        a.e(add(X13, x, X15));
        a.e(ldurb(X16, X13, 4));
        a.e(lsl_imm(RESULT, X16, 3));
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
    // A suffix ref's offset, and its owner, a bloblet (`TODO.md` §77).
    if name == "%suffix-ref-offset" || name == "%suffix-ref-owner" {
        a.e(and_low(X16, x, 3));
        a.e(cmp_imm(X16, fixpt_heap::value::TAG_SUFFIX_REF as u32));
        a.to(slow, Fix::If(Cond::Ne));
        if name == "%suffix-ref-offset" {
            a.e(lsr_imm(X13, x, fixpt_heap::value::SUFFIX_OFFSET_SHIFT));
            a.e(lsl_imm(RESULT, X13, 3));
        } else {
            a.e(ubfx(X14, x, 3, fixpt_heap::value::SUFFIX_OWNER_BITS));
            a.e(ldr(X9, ST, st_off(offset_of!(DState, words))));
            a.e(add_lsl(X11, X9, X14, 3));
            a.e(add_imm(RESULT, X11, fixpt_heap::value::TAG_BLOBLET as u32));
        }
        return true;
    }
    // `y` bytes along: still in the owner's suffix, the offset rebuilt.
    if name == "%suffix-ref+" {
        fixnum(a, y);
        suffix_owner(a, x, slow);
        a.e(asr_imm(X9, y, 3));
        a.e(add(X9, X15, X9));
        a.e(cmp(X9, X13));
        a.to(slow, Fix::If(Cond::Hs));
        a.e(ubfx(X14, x, 0, fixpt_heap::value::SUFFIX_OFFSET_SHIFT));
        a.e(lsl_imm(X9, X9, fixpt_heap::value::SUFFIX_OFFSET_SHIFT));
        a.e(orr(RESULT, X14, X9));
        return true;
    }
    let Some(rest) = name.strip_prefix("%fx26-") else { return false };
    if let Some(what) = rest.strip_prefix("f32") {
        return f32_fast(a, what, y);
    }
    // The fixnum-shaped widths: whether signed, and their bits.
    let width = |t: &str| match t {
        "i8" => Some((true, 8)),
        "u8" => Some((false, 8)),
        "i32" => Some((true, 32)),
        "u32" => Some((false, 32)),
        _ => None,
    };
    if let Some((s, bits)) = rest.strip_prefix("int->").and_then(width) {
        fixnum(a, x);
        wrap_small(a, s, bits);
        return true;
    }
    let Some((s, bits, op)) = ["i8", "u8", "i32", "u32"]
        .iter()
        .find_map(|t| rest.strip_prefix(t).filter(|op| !op.starts_with(|c: char| c.is_ascii_digit())).and_then(|op| width(t).map(|(s, b)| (s, b, op))))
    else {
        return false;
    };
    let wrap = |a: &mut Asm, s: bool| wrap_small(a, s, bits);
    let test = match op {
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
    match op {
        "->int" => {}
        "+" => {
            a.e(add(RESULT, x, y));
            wrap(a, s);
        }
        "-" => {
            a.e(sub(RESULT, x, y));
            wrap(a, s);
        }
        "*" => {
            a.e(asr_imm(X13, y, 3));
            a.e(mul(RESULT, x, X13));
            wrap(a, s);
        }
        "-quotient" => {
            nonzero(a);
            a.e(sdiv(X13, x, y));
            a.e(lsl_imm(RESULT, X13, 3));
            wrap(a, s);
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
            wrap(a, s);
        }
        "-shl" => {
            fixnum(a, y);
            a.e(ubfx(X13, y, 3, bits.trailing_zeros()));
            a.e(lslv(RESULT, x, X13));
            wrap(a, s);
        }
        // An arithmetic or logical shift right, the tag's bits cleared.
        "-shr" => {
            fixnum(a, y);
            a.e(ubfx(X13, y, 3, bits.trailing_zeros()));
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
    // Past 8, the eighth is a list of the rest (Larceny's convention). The
    // vector kept from the last call-out, not a new one each time: making
    // and freeing it was a fifth of a run that calls out often (`mlton/
    // peek`). A call-out within this one takes an empty one.
    let mut args: Vec<Value> = CALLOUT_ARGS.take();
    args.clear();
    args.extend(st.args[..n.min(8)].iter().map(|a| Value::from_raw(*a)));
    if n > 8 {
        let mut rest = args.pop().expect("eight");
        while args.len() < n {
            args.push(rt.heap.car(rest));
            rest = rt.heap.cdr(rest);
        }
    }
    if let Callout::Foreign = c {
        args.push(Value::from_raw(st.aux));
    }
    let mut code = [Value::from_raw(st.code)];
    // The frames walked only for a collection; none for a primitive that
    // never collects, whose caller's values are in registers.
    let quiet = matches!(c, Callout::Pure { .. } | Callout::Box { .. } | Callout::Unbox | Callout::BoxF64 | Callout::Underflow | Callout::Overflow | Callout::PollDone | Callout::Failed);
    // A collection, Larceny's way (`docs/research/deep-recursion.md`): the
    // run's frames flushed into the heap first, so that the collector reads
    // no stack; then the innermost restored, where the code goes on.
    if !quiet && rt.heap.collection_due() {
        flush_all(&mut rt.heap, st);
        let mut cont = [Value::from_raw(st.cont)];
        rt.heap.collect_due(&mut [&mut args, &mut code, &mut cont]);
        st.cont = cont[0].raw();
        match restore(&rt.heap, st, cont_pos(st), st.cont_words) {
            Ok((lo, _)) => (st.fp, st.native_sp) = (lo + R_LINK, lo),
            Err(why) => return failed(st, why),
        }
    }
    let out = match c {
        Callout::Cons => rt.heap.cons(args[0], args[1]).raw(),
        Callout::Bloblet => match bloblet_sizes(args[0], args[1]) {
            Some((bytes, fields)) => rt.heap.make_bloblet(fixpt_heap::layout::kind("bloblet"), fields, bytes, true).raw(),
            None => {
                let (b, f) = (fixpt_engine::cellular::describe(rt, args[0]), fixpt_engine::cellular::describe(rt, args[1]));
                LAST_MESSAGE.with(|c| *c.borrow_mut() = Some(format!("bloblet: no bloblet of {b} bytes and {f} fields")));
                st.trap = PRIM_FAILED as u64;
                0
            }
        },
        Callout::Box { signed } => {
            let bits = args[0].raw();
            fixpt_runtime::integer_value(rt, if signed { bits as i64 as i128 } else { bits as i128 }).raw()
        }
        Callout::Unbox => fixpt_runtime::low_64_bits(rt, args[0]),
        Callout::BoxF64 => rt.heap.make_flonum(f64::from_bits(args[0].raw())).raw(),
        Callout::Closure { .. } | Callout::ClosureAny => native_closure(&mut rt.heap, Value::from_raw(st.aux), &args).raw(),
        Callout::RegionClosure { n } => {
            let h = if args[0].is_fixnum() { args[0].as_fixnum() as usize } else { usize::MAX };
            let (free, code) = (&args[1..n - 1], args[n - 1]);
            rt.heap.in_region(h, |heap| native_closure(heap, code, free)).raw()
        }
        Callout::Foreign => {
            let (f, args) = args.split_last().expect("the callee");
            call_foreign(rt, st, *f, args, None)
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
        Callout::Failed => {
            st.aux = 0;
            let code = st.trap as usize;
            let past = THROWN.with(|t| t.get()).is_some() || ABORTED.with(|a| a.get()).is_some();
            if code == OUT_OF_FUEL as usize || code >= TRAPS.len() && code != PRIM_FAILED as usize || past {
                return 0;
            }
            let message = match LAST_MESSAGE.with(|m| m.borrow_mut().take()) {
                Some(m) => m,
                None => TRAPS.get(code).copied().unwrap_or("a primitive failed").to_string(),
            };
            let st_ref = &*st;
            let tag = fixpt_runtime::sched::task_failed(rt, &message, |rt, tag| has_prompt(&rt.heap, st_ref, tag));
            match tag {
                Some(tag) => {
                    let unit = rt.heap.intern_static("#u");
                    if abort_to(rt, st, tag, unit) {
                        (st.trap, st.aux) = (0, 1);
                    }
                }
                None if code == PRIM_FAILED as usize => LAST_MESSAGE.with(|m| *m.borrow_mut() = Some(message)),
                None => {}
            }
            0
        }
        Callout::PollDone => {
            fixpt_runtime::sched::preempt_done(rt);
            0
        }
        Callout::Poll => {
            let take = st.reserve.min(fixpt_runtime::sched::slice());
            (st.fuel, st.reserve) = (take, st.reserve - take);
            let own = |h: &Heap, f: Value| DirectMachine::compiled_of(h, f).is_some();
            // Beyond this run's frames, those of the machines out from it
            // (`fixpt_runtime::crossing`), asked first.
            let beyond = fixpt_runtime::crossing::crossed()
                && fixpt_runtime::sched::prompt_tag(&rt.heap).is_some_and(|t| fixpt_runtime::crossing::reachable(rt, t));
            let due = fixpt_runtime::sched::preempt_due(rt, own, |rt, tag| beyond || has_prompt(&rt.heap, st, tag));
            st.aux = due.map_or(0, |f| f.raw());
            0
        }
        Callout::Underflow => match restore(&rt.heap, st, cont_pos(st), st.cont_words) {
            Ok((lo, pc)) => {
                st.stats.underflows += 1;
                (st.resume_sp, st.resume_fp, st.resume_pc) = (lo, lo + R_LINK, pc);
                0
            }
            Err(why) => failed(st, why),
        },
        Callout::Overflow => {
            let r = overflow(&mut rt.heap, st);
            st.words = rt.heap.words_address() as u64;
            r
        }
        Callout::Capture { whole, once } => {
            // `f`, moved by a collection, where the code reads it.
            st.args[0] = args[0].raw();
            let k = if whole {
                Some(capture_whole(rt, st))
            } else {
                capture_delimited(rt, st, args[1])
            };
            match k {
                Some(k) => {
                    if once {
                        rt.heap.make_one_shot(k);
                    }
                    k.raw()
                }
                None => failed(st, "call-with-composable-continuation: no prompt for this tag".into()),
            }
        }
        Callout::Reinstate => reinstate(rt, st, args[1], args[0]),
        Callout::Rest => rt.heap.list_from(&args).raw(),
        Callout::FirstMark => all_marks(rt, st, args[0]).first().copied().unwrap_or(args[1]).raw(),
        Callout::CurrentMarks => {
            let marks = all_marks(rt, st, args[0]);
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
    CALLOUT_ARGS.set(args);
    out
}

/// What is not native code, `f`, called with `args` from the frames at
/// `st.fp` on: its value; or, back with an abort to a prompt in those
/// frames, where `common_foreign` resumes (`foreign_resume`); or a trap.
/// While it runs, the frames' values are kept where the heap roots them,
/// and the call is a boundary a capture crosses (`capture_foreign`).
///
/// The frames' innermost is the stub's (`common_foreign`), whose return is
/// where they resume with the value; or, `resume` given, the frames are a
/// continuation's just put back (`reinstate`), resuming there.
fn call_foreign(rt: &mut fixpt_runtime::Runtime, st: &mut DState, f: Value, args: &[Value], resume: Option<u64>) -> u64 {
    if !fixpt_runtime::crossing::room() {
        LAST_MESSAGE.with(|c| *c.borrow_mut() = Some(fixpt_engine::cellular::Trap::StackOverflow.to_string()));
        st.trap = PRIM_FAILED as u64;
        return 0;
    }
    let held: Vec<Value> = native_frames(st).iter().flat_map(|s| s.iter().copied()).collect();
    let kept = rt.heap.vector_from(&held);
    let at = rt.heap.push_root(kept);
    rt.heap.push_root(Value::from_raw(st.cont));
    // A native call from the cellular code runs below these frames.
    let runner = RUNNING.get().expect("native code is running");
    let outer = CALLED_OUT.replace(Some((runner, st.native_sp)));
    let boundary = std::rc::Rc::new(Foreign { st: st as *mut DState, at, resume });
    let r = fixpt_runtime::crossing::across(boundary, || fixpt_engine::cellular::call_value(rt, f, args));
    CALLED_OUT.set(outer);
    put_back(rt, st, at);
    rt.heap.pop_roots_to(at);
    match r {
        Ok(v) => v.raw(),
        Err(e) => {
            match e {
                fixpt_runtime::NativeExit::Failed(m) => LAST_MESSAGE.with(|c| *c.borrow_mut() = Some(m)),
                // A whole continuation: this run, if it is the bottom
                // machine's, gives it its value, its frames replaced, and
                // `common_foreign` resumes where it says; else on out.
                fixpt_runtime::NativeExit::Throw { k, v } => {
                    let bottom = !fixpt_runtime::crossing::crossed();
                    if bottom && rt.heap.native_continuation_of(k).is_some() {
                        reinstate(rt, st, k, v);
                        if st.trap == 0 {
                            st.foreign_resume = 1;
                        }
                        return 0;
                    }
                    THROWN.with(|t| t.set(Some((k, v))));
                    let why = if bottom { "a whole continuation of cellular code, given a value under native code it did not take" } else { "a whole continuation thrown out to the machine at the bottom" };
                    LAST_MESSAGE.with(|c| *c.borrow_mut() = Some(why.into()));
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

/// A run of native code in a call of what is not native code
/// (`call_foreign`): its call-out's state, and where the heap keeps the
/// values of its frames meanwhile.
struct Foreign {
    st: *mut DState,
    at: usize,
    resume: Option<u64>,
}

impl Foreign {
    /// Its frames out from the call, and where the innermost resumes: past
    /// the stub's, at its return; or all of them, at `resume`.
    fn frames(&self, st: &DState) -> (Vec<(u64, u64)>, u64) {
        let all = frames_of(st);
        match self.resume {
            Some(pc) => (all, pc),
            None => (all[1..].to_vec(), word(all[0].0 + R_SECOND)),
        }
    }
}

impl fixpt_runtime::crossing::Crossing for Foreign {
    fn capture(&self, rt: &mut fixpt_runtime::Runtime, tag: Value, inner: Value) -> fixpt_runtime::crossing::Crossed {
        // SAFETY: the state of the call-out that made this boundary, which
        // is in this call, and holds no reference to it meanwhile.
        capture_foreign(rt, unsafe { &mut *self.st }, self, tag, inner)
    }

    /// All its frames, from the stub's out, resumed where the call returns:
    /// whole, if this run is the bottom machine's.
    fn capture_whole(&self, rt: &mut fixpt_runtime::Runtime, bottom: bool, inner: Value) -> Value {
        // SAFETY: as for `capture`.
        let st = unsafe { &mut *self.st };
        put_back(rt, st, self.at);
        let (frames, pc) = self.frames(st);
        let frames = &frames[..];
        let p = if frames.is_empty() {
            cont_pos(st)
        } else {
            let last = outermost_second(st, frames.last().expect("a frame").0);
            let mut p = heap_frames(&mut rt.heap, frames, last, cont_pos(st));
            p.pc = pc;
            p
        };
        let words = region_words(frames) + st.cont_words;
        // None between: at the bottom, still a whole continuation, of no
        // frames, which returns from the run (`put_continuation`).
        if words == 0 && !bottom {
            return inner;
        }
        let code = continuation_bloblet(&mut rt.heap);
        continuation(rt, code, if words == 0 { END } else { p }, words, bottom, inner)
    }

    fn has_prompt(&self, rt: &mut fixpt_runtime::Runtime, tag: Value) -> (bool, bool) {
        // SAFETY: as for `capture`.
        let st = unsafe { &mut *self.st };
        put_back(rt, st, self.at);
        (has_prompt(&rt.heap, st, tag), true)
    }

    /// Its frames' marks, and on: a machine in a call, if there is one, is
    /// the one that called this run (`call_native`).
    fn marks(&self, rt: &mut fixpt_runtime::Runtime, key: Value) -> (Vec<Value>, bool) {
        // SAFETY: as for `capture`.
        let st = unsafe { &mut *self.st };
        put_back(rt, st, self.at);
        (run_marks(&rt.heap, st, key), true)
    }
}

/// The values of the frames from `st.fp` on, and the chain, as the heap
/// has kept them from `at` (`call_foreign`), moved, put back.
fn put_back(rt: &mut fixpt_runtime::Runtime, st: &mut DState, at: usize) {
    let kept = rt.heap.root_at(at);
    st.cont = rt.heap.root_at(at + 1).raw();
    let mut i = 0;
    for s in native_frames(st) {
        for v in s.iter_mut() {
            *v = rt.heap.obj_ref(kept, i);
            i += 1;
        }
    }
}

/// A capture crossing a call of what is not native code (`call_foreign`,
/// `fixpt_runtime::crossing`): the frames that made it, from the stub's
/// out to the innermost prompt for `tag`, or all of them, with `inner`
/// inside, resumed where the call returns; or `inner`, if none are
/// between. The frames' values first as the heap has kept them, moved.
fn capture_foreign(rt: &mut fixpt_runtime::Runtime, st: &mut DState, b: &Foreign, tag: Value, inner: Value) -> fixpt_runtime::crossing::Crossed {
    use fixpt_runtime::crossing::Crossed;
    put_back(rt, st, b.at);
    let (frames, pc) = b.frames(st);
    let frames = &frames[..];
    let code = continuation_bloblet(&mut rt.heap);
    if let Some(j) = frames.iter().position(|&(fp, end)| is_control(fp, end, PROMPT_MARK, tag)) {
        if j == 0 {
            return Crossed::Found(inner);
        }
        let last = word(frames[j - 1].0 + R_SECOND);
        let mut p = heap_frames(&mut rt.heap, &frames[..j], last, END);
        p.pc = pc;
        return Crossed::Found(continuation(rt, code, p, region_words(&frames[..j]), false, inner));
    }
    let recs = records(&rt.heap, cont_pos(st));
    let (tail, words, found) = match recs.iter().position(|r| r.is_control(PROMPT_MARK, tag)) {
        Some(j) => (copy_records(&mut rt.heap, &recs[..j], END).0, recs[..j].iter().map(|r| r.n as u64).sum::<u64>(), true),
        None => (cont_pos(st), st.cont_words, false),
    };
    let p = if frames.is_empty() {
        tail
    } else {
        let last = outermost_second(st, frames.last().expect("a frame").0);
        let mut p = heap_frames(&mut rt.heap, frames, last, tail);
        p.pc = pc;
        p
    };
    let words = words + region_words(frames);
    let k = if words == 0 { inner } else { continuation(rt, code, p, words, false, inner) };
    if found { Crossed::Found(k) } else { Crossed::Beyond(k) }
}

thread_local! {
    /// The vector a call-out's arguments are gathered into, kept between
    /// call-outs (`callout`).
    static CALLOUT_ARGS: std::cell::Cell<Vec<Value>> = const { std::cell::Cell::new(Vec::new()) };
}

/// The innermost prompt for `tag` in the chain from `p`, and how many words
/// of frames are newer than it.
fn chain_prompt(heap: &Heap, p: Pos, tag: Value) -> Option<(Rec, u64)> {
    let mut dropped = 0;
    for r in records(heap, p) {
        if r.is_control(PROMPT_MARK, tag) {
            return Some((r, dropped));
        }
        dropped += r.n as u64;
    }
    None
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
        None => match chain_prompt(&rt.heap, cont_pos(st), tag) {
            Some((r, dropped)) => match restore(&rt.heap, st, r.pos(), st.cont_words.saturating_sub(dropped)) {
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
            rt.heap.regions_exit_to(Value::from_raw(word(pf + R_HEAD + 24)).as_fixnum() as usize);
            (st.resume_sp, st.resume_fp, st.resume_pc, st.resume_x0) = (pf, pf + R_LINK, word(pf + R_SECOND), v.raw());
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
/// `top`) on, as their regions: from the header word below each one's link
/// to the next one's (`STUB_FRAME`), the outermost's to `top`.
fn frames_from(mut fp: u64, top: u64) -> impl Iterator<Item = (u64, u64)> {
    std::iter::from_fn(move || {
        if fp < R_LINK || fp - R_LINK >= top {
            return None;
        }
        let lo = fp - R_LINK;
        let caller = word(fp);
        let hi = if caller > fp && caller - R_LINK <= top { caller - R_LINK } else { top };
        fp = if hi + R_LINK == caller { caller } else { 0 };
        Some((lo, hi))
    })
}

/// Whether the frame at `fp` is a control frame of `marker` for `key`.
fn is_control(lo: u64, hi: u64, marker: Value, key: Value) -> bool {
    hi - lo == CONTROL_FRAME && word(lo + R_HEAD) == marker.raw() && word(lo + R_HEAD + 8) == key.raw()
}

/// A place in the stack cache's chain: a frame (a native frame in the
/// heap, `TODO.md` §91), and where it resumes; or the chain's end (`#f`).
#[derive(Clone, Copy)]
struct Pos {
    frame: Value,
    pc: u64,
}

const END: Pos = Pos::new(Value::FALSE, 0);

impl Pos {
    const fn new(frame: Value, pc: u64) -> Pos {
        Pos { frame, pc }
    }
}

/// The rest of this run's frames, in the heap.
fn cont_pos(st: &DState) -> Pos {
    Pos::new(Value::from_raw(st.cont), st.cont_pc)
}

fn set_cont(st: &mut DState, p: Pos, words: u64) {
    (st.cont, st.cont_pc, st.cont_words) = (p.frame.raw(), p.pc, words);
}

/// A frame of the chain: the native frame, its words (its header's
/// included, as on the stack), its second word, where it resumes, and
/// where its fields are: nothing collects while the chain is walked, so
/// they stay where they are.
#[derive(Clone, Copy)]
struct Rec {
    frame: Value,
    n: usize,
    w8: u64,
    pc: u64,
    fields: *const u64,
    nfields: usize,
    raw: *const u64,
}

impl Rec {
    /// Its `j`th word from its third on (its map, or its marker).
    fn word(&self, j: usize) -> Value {
        // SAFETY: one of its fields (`j < n - 3`), which do not move while
        // the chain is walked.
        Value::from_raw(unsafe { *self.fields.add(2 + j) })
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
        Pos::new(self.frame, self.pc)
    }
    /// The address just past it, in the heap: where the next frame out
    /// mostly starts.
    fn end(&self) -> u64 {
        self.raw as u64 + 8 * (self.n - 1 - self.nfields) as u64
    }
}

/// The frame at `p`, and the place after it; none at the chain's end.
fn step(heap: &Heap, p: Pos) -> Option<(Rec, Pos)> {
    step_after(heap, p, 0)
}

/// [`step`], the frame looked for first where the one before it, `after`,
/// ends ([`Rec::end`]): a chain's frames often lie in order.
fn step_after(heap: &Heap, p: Pos, after: u64) -> Option<(Rec, Pos)> {
    if p.frame == Value::FALSE {
        return None;
    }
    let (w, raw) = heap.native_frame_parts_after(p.frame, after);
    let (next, w8) = (Value::from_raw(w[0]), Value::from_raw(w[1]).as_fixnum() as u64);
    let r = Rec { frame: p.frame, n: 1 + w.len() + raw.len(), w8, pc: p.pc, fields: w.as_ptr(), nfields: w.len(), raw: raw.as_ptr() };
    Some((r, Pos::new(next, w8)))
}

/// Each frame of the chain from `p`, newest first.
fn records(heap: &Heap, mut p: Pos) -> Vec<Rec> {
    let mut out = Vec::new();
    let mut after = 0;
    while let Some((r, q)) = step_after(heap, p, after) {
        out.push(r);
        (p, after) = (q, r.end());
    }
    out
}

/// The shape of the frame whose region is `lo` to `hi`, as its bloblet
/// will be: how many fields (its link, its second word, its map or marker,
/// its values), the rest of it raw words, its suffix (`TODO.md` §91); and
/// the mask of its fields from the third on that are values to keep (the
/// third itself, the map or a control frame's marker, always; all of one
/// too wide for a map). What it leaves out, dead or not a value, a flush
/// keeps as the fixnum 0.
fn frame_shape(lo: u64, hi: u64) -> (usize, u64) {
    let n = ((hi - lo) / 8) as usize;
    // A stub's: its link, its return and a word to align it, none kept.
    if hi - lo <= STUB_FRAME {
        return (n - 1, 0);
    }
    let head = Value::from_raw(word(lo + R_HEAD));
    // A control frame: its marker and the three words after it, not its
    // padding.
    if !head.is_fixnum() {
        return (n - 1, 0b1111);
    }
    match head.as_fixnum() {
        // Too wide for a map: every value.
        m if m < 0 => ((-m) as usize, u64::MAX),
        m => ((m as u64 >> MAP_BITS) as usize, (m as u64 & ((1 << MAP_BITS) - 1)) << 1 | 1),
    }
}

/// The stack's `frames`, innermost first, copied into the heap onto the
/// chain at `tail` (older than they), each a native frame: as it was, its
/// link the next out, its second word a fixnum, its dead words 0; the
/// outermost's second word `last` (where the chain at `tail` resumes, if
/// that frame's own says the underflow). Where the innermost is, its `pc`
/// for the caller to say. Allocates and never collects, so what the frames
/// and `tail` hold stays where it is.
fn heap_frames(heap: &mut Heap, frames: &[(u64, u64)], last: u64, tail: Pos) -> Pos {
    let outermost = frames.len() - 1;
    let mut next = tail.frame;
    for (f, &(lo, hi)) in frames.iter().enumerate().rev() {
        let (fields, mask) = frame_shape(lo, hi);
        let second = if f == outermost { last } else { word(lo + R_SECOND) };
        let link = next;
        // SAFETY: the frame's raw words, on the native stack.
        let raw = unsafe { std::slice::from_raw_parts((lo + 8 * (1 + fields as u64)) as *const u64, ((hi - lo) / 8) as usize - 1 - fields) };
        next = heap.native_frame_with(fields, raw, |i| match i {
            0 => link,
            1 => Value::fixnum(second as i64),
            _ => {
                let j = i - 2;
                let at = lo + 8 * (i as u64 + 1);
                if j >= 64 || mask & (1 << j) != 0 { Value::from_raw(word(at)) } else { Value::fixnum(0) }
            }
        });
    }
    Pos::new(next, 0)
}

/// The second word the outermost of this run's frames on the stack should
/// have in the chain: where the chain resumes, if there is one (the frame's
/// own says the underflow), else its own (the bottom's).
fn outermost_second(st: &DState, outermost: u64) -> u64 {
    if step_nonempty(st) { st.cont_pc } else { word(outermost + R_SECOND) }
}

fn step_nonempty(st: &DState) -> bool {
    st.cont != Value::FALSE.raw()
}

/// Frames restored from the chain at `p`, of `chain` words, onto the run's empty stack cache,
/// at its top: at least one, and on to `RESTORE_WORDS`, never ending with
/// one its code pops (whose code is in the frame outside it), nor above a
/// mark in tail position (which a mark in tail position in the frame above
/// it finds directly under its own, to replace). The last links and
/// returns to the bottom if the chain ends there, else returns through the
/// underflow. The rest of the chain is the run's. Where the innermost is,
/// and where it resumes.
fn restore(heap: &Heap, st: &mut DState, p: Pos, chain: u64) -> Result<(u64, u64), String> {
    let (mut recs, mut words, mut q, mut after) = (Vec::with_capacity(64), 0, p, 0);
    while let Some((r, nq)) = step_after(heap, q, after) {
        let returns = r.returns();
        recs.push((r, returns));
        words += r.n;
        (q, after) = (nq, r.end());
        if words >= RESTORE_WORDS && returns && !step_after(heap, q, after).is_some_and(|(r2, _)| r2.is_tail_mark()) {
            break;
        }
    }
    if recs.is_empty() {
        return Err("the stack cache has nothing to restore".into());
    }
    let more = q.frame != Value::FALSE;
    let (link, ret) = if more { (0, st.underflow) } else { (st.bottom_link, st.bottom_ret) };
    let base = place(st, &recs, words, st.stack_top, link, ret)?;
    set_cont(st, if more { q } else { END }, if more { chain.saturating_sub(words as u64) } else { 0 });
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
    let mut lo = base;
    for (i, &(r, returns)) in recs.iter().enumerate() {
        let last = i + 1 == recs.len();
        put_frame(r, lo, if last { link } else { lo + 8 * r.n as u64 + R_LINK }, if last && returns { ret } else { r.w8 });
        lo += 8 * r.n as u64;
    }
    Ok(base)
}

/// Frame `r` put on the stack, its region at `lo`, linking to `link`, its
/// second word `second`.
fn put_frame(r: Rec, lo: u64, link: u64, second: u64) {
    set_word(lo + R_LINK, link);
    set_word(lo + R_SECOND, second);
    // SAFETY: words of the native stack, above its limit, which no Rust
    // code holds while the call-out runs; the frame's fields, in the heap.
    unsafe {
        std::ptr::copy_nonoverlapping(r.fields.add(2), (lo + R_HEAD) as *mut u64, r.nfields - 2);
        std::ptr::copy_nonoverlapping(r.raw, (lo + 8 * (1 + r.nfields as u64)) as *mut u64, r.n - 1 - r.nfields);
    }
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
    let (f0, top) = (st.fp - R_LINK, st.stack_top);
    // The frames kept: this one, and the marks in tail position it is
    // under, which a mark in tail position in it finds directly under its
    // frame, to replace (`withmark-tail`).
    let mut keep: Vec<(u64, u64)> = Vec::new();
    for (fp, end) in frames_from(st.fp, top) {
        if keep.is_empty() || is_tail_mark(fp, end) {
            keep.push((fp, end));
        } else {
            break;
        }
    }
    let (outer, kept_end) = *keep.last().expect("this frame");
    let caller = word(outer + R_LINK);
    if !(caller > outer + R_LINK && caller - R_LINK < top && caller - R_LINK == kept_end) {
        return failed(st, "stack overflow".into());
    }
    let size = kept_end - f0;
    let frames: Vec<(u64, u64)> = frames_from(caller, top).collect();
    let words: u64 = frames.iter().map(|&(a, b)| (b - a) / 8).sum();
    if st.cont_words + words + size / 8 > st.max_words {
        return failed(st, "stack overflow".into());
    }
    // The kept frames aside, to move them; the marks' words are values to
    // keep.
    let mut kept: Vec<Value> = (0..size / 8).map(|i| Value::from_raw(word(f0 + 8 * i))).collect();
    let last = outermost_second(st, frames.last().expect("a frame").0);
    let mut p = flush_in_place(heap, &frames, last, cont_pos(st));
    p.pc = kept[((outer + R_SECOND - f0) / 8) as usize].raw();
    set_cont(st, p, st.cont_words + words);
    st.stats.overflows += 1;
    st.stats.frames_flushed += frames.len() as u64;
    st.stats.words_flushed += words;
    // The collection: the roots, what the entry holds (`overflow_info`).
    let info = st.overflow_info;
    let variadic = info & 1 << 9 != 0;
    let n = if variadic { (st.nargs as usize).min(8) } else { (info & 0xff) as usize };
    let mut regs: Vec<Value> = (1..=n).map(|r| Value::from_raw(st.kept[r])).collect();
    let mut saved: Vec<Value> = if variadic { st.args[..n].iter().map(|a| Value::from_raw(*a)).collect() } else { Vec::new() };
    let mut clo: Vec<Value> = if info & 1 << 8 != 0 { vec![Value::from_raw(st.kept[CLO as usize])] } else { Vec::new() };
    let mut code = [Value::from_raw(st.overflow_code), Value::from_raw(st.code)];
    let mut cont = [Value::from_raw(st.cont)];
    {
        let mut roots: Vec<&mut [Value]> = vec![&mut regs, &mut saved, &mut clo, &mut code, &mut cont];
        // The marks' words, from the third on, in each kept frame but this.
        let mut rest: &mut [Value] = &mut kept;
        let mut at = 0u64;
        for &(fp, end) in &keep {
            let n = ((end - fp) / 8) as usize;
            let (this, more) = rest.split_at_mut(n);
            if fp != f0 {
                roots.push(&mut this[3..7]);
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
    for &(lo, _) in &keep[..keep.len() - 1] {
        set_word(moved(lo) + R_LINK, moved(word(moved(lo) + R_LINK)));
    }
    set_word(moved(outer) + R_LINK, 0);
    set_word(moved(outer) + R_SECOND, st.underflow);
    (st.resume_sp, st.resume_fp) = (to, to + R_LINK);
    0
}

/// The stack's `frames`, innermost first, contiguous and the run's last,
/// made the chain's newest frames onto `tail` where they are (Larceny's
/// flush in place): each a native frame, its header written in the word
/// below its link, its link the next out, its second word a fixnum (the
/// outermost's `last`), its dead words 0. Objects of the nursery, which the
/// collection that must follow moves out. Where the innermost is, its `pc`
/// for the caller to say.
fn flush_in_place(heap: &mut Heap, frames: &[(u64, u64)], last: u64, tail: Pos) -> Pos {
    // From the outermost in, each linking to the one made before it;
    // nothing collects until all of them are made.
    let outermost = frames.len() - 1;
    let mut next = tail.frame;
    for (f, &(lo, hi)) in frames.iter().enumerate().rev() {
        let (fields, mask) = frame_shape(lo, hi);
        let second = if f == outermost { last } else { word(lo + R_SECOND) };
        set_word(lo + R_LINK, next.raw());
        set_word(lo + R_SECOND, Value::fixnum(second as i64).raw());
        for j in 0..fields - 2 {
            if j < 64 && mask & (1 << j) == 0 {
                set_word(lo + R_HEAD + 8 * j as u64, Value::fixnum(0).raw());
            }
        }
        next = heap.native_frame_in_place(lo, fields, ((hi - lo) / 8) as usize - 1 - fields);
    }
    Pos::new(next, 0)
}

/// Every frame of the run on the stack, from the one that called out (at
/// `st.fp`, the stack's pointer too), flushed where it is onto the chain,
/// leaving the stack empty: for a collection, which moves them out, after
/// which `restore` puts the innermost back. Where the innermost resumes is
/// not kept: the call-out returns to it.
fn flush_all(heap: &mut Heap, st: &mut DState) {
    debug_assert_eq!(st.fp, st.native_sp + R_LINK, "a call-out's frame is the stack's top");
    let frames = frames_of(st);
    let Some(&(outer, _)) = frames.last() else { return };
    let words: u64 = frames.iter().map(|&(a, b)| (b - a) / 8).sum();
    let last = outermost_second(st, outer);
    let p = flush_in_place(heap, &frames, last, cont_pos(st));
    set_cont(st, p, st.cont_words + words);
    st.stats.collection_flushes += 1;
    st.stats.frames_flushed += frames.len() as u64;
    st.stats.words_flushed += words;
}

/// Whether the frame from `fp` to `end` is a mark's in tail position: a
/// control frame of `MARK_MARK` left by a return to its second word.
fn is_tail_mark(lo: u64, hi: u64) -> bool {
    hi - lo == CONTROL_FRAME && word(lo + R_HEAD) == MARK_MARK.raw() && word(lo + R_SECOND) != 0
}

/// A continuation's data, around `p`, the chain of its frames, its code
/// `code` (the continuation procedure's); with the continuation of another
/// machine's frames inside it, `inner`, if not `#f` (`reinstate`).
fn continuation(rt: &mut fixpt_runtime::Runtime, code: Value, p: Pos, words: u64, whole: bool, inner: Value) -> Value {
    let heap = &mut rt.heap;
    let regions = Value::fixnum(heap.live_regions() as i64);
    let data = [CONT_MARK, p.frame, Value::fixnum(words as i64), Value::fixnum(p.pc as i64), regions, Value::boolean(whole), inner, fixpt_heap::Shots::Many.value()];
    debug_assert_eq!(data.len(), fixpt_heap::NATIVE_CONT_LEN);
    let data = heap.vector_from(&data);
    native_closure(heap, code, &[data])
}

/// A continuation's chain, and how many words of frames it holds.
fn continuation_pos(heap: &Heap, data: Value) -> (Pos, u64) {
    (Pos::new(heap.obj_ref(data, 1), heap.obj_ref(data, 3).as_fixnum() as u64), heap.obj_ref(data, 2).as_fixnum() as u64)
}

/// The whole continuation of the frames from the one that called out,
/// resumed where the state's `ret_pc` says: a native closure of the
/// continuation procedure (the state's `aux`) over its chain, the frames on
/// the stack copied onto the run's.
fn capture_whole(rt: &mut fixpt_runtime::Runtime, st: &DState) -> Value {
    let frames = frames_of(st);
    let last = outermost_second(st, frames.last().expect("a frame").0);
    let mut p = heap_frames(&mut rt.heap, &frames, last, cont_pos(st));
    p.pc = st.ret_pc;
    // A machine called this run: this run's frames are a piece of the
    // whole, every machine's out to the bottom one's
    // (`fixpt_runtime::crossing::capture_whole`).
    let crossed = fixpt_runtime::crossing::crossed();
    let own = continuation(rt, Value::from_raw(st.aux), p, region_words(&frames) + st.cont_words, !crossed, Value::FALSE);
    if crossed { fixpt_runtime::crossing::capture_whole(rt, own) } else { own }
}

/// A continuation's frames, delimited by the innermost prompt for `tag`:
/// those on the stack before it; or all of them and a copy of the chain's
/// before it; none if no prompt for `tag` is in this run.
/// Whether the prompt of `tag` is among this run's frames, on the stack or
/// in its chain, which a capture up to it would reach (`Callout::Poll`).
fn has_prompt(heap: &Heap, st: &DState, tag: Value) -> bool {
    frames_of(st).iter().any(|&(fp, end)| is_control(fp, end, PROMPT_MARK, tag))
        || records(heap, cont_pos(st)).iter().any(|r| r.is_control(PROMPT_MARK, tag))
}

fn capture_delimited(rt: &mut fixpt_runtime::Runtime, st: &DState, tag: Value) -> Option<Value> {
    let frames = frames_of(st);
    if let Some(j) = frames.iter().position(|&(fp, end)| is_control(fp, end, PROMPT_MARK, tag)) {
        let last = word(frames[j - 1].0 + R_SECOND);
        let mut p = heap_frames(&mut rt.heap, &frames[..j], last, END);
        p.pc = st.ret_pc;
        return Some(continuation(rt, Value::from_raw(st.aux), p, region_words(&frames[..j]), false, Value::FALSE));
    }
    let recs = records(&rt.heap, cont_pos(st));
    let found = recs.iter().position(|r| r.is_control(PROMPT_MARK, tag));
    // None in this run: every frame of it, and those of the machines out
    // from it up to the prompt, if a machine called it (`crossing`).
    if found.is_none() && !fixpt_runtime::crossing::crossed() {
        return None;
    }
    let (tail, words) = match found {
        Some(j) => (copy_records(&mut rt.heap, &recs[..j], END).0, recs[..j].iter().map(|r| r.n as u64).sum::<u64>()),
        None => (cont_pos(st), st.cont_words),
    };
    let last = outermost_second(st, frames.last().expect("a frame").0);
    let mut p = heap_frames(&mut rt.heap, &frames, last, tail);
    p.pc = st.ret_pc;
    let k = continuation(rt, Value::from_raw(st.aux), p, region_words(&frames) + words, false, Value::FALSE);
    if found.is_some() {
        return Some(k);
    }
    fixpt_runtime::crossing::capture(rt, tag, k)
}

/// Frames `recs` of a chain copied onto `tail`, each a new native frame;
/// and the outermost copied.
fn copy_records(heap: &mut Heap, recs: &[Rec], tail: Pos) -> (Pos, Value) {
    let (mut next, mut outermost) = (tail.frame, Value::FALSE);
    for r in recs.iter().rev() {
        let link = next;
        // SAFETY: its fields, which do not move: nothing collects here.
        let raw = unsafe { std::slice::from_raw_parts(r.raw, r.n - 1 - r.nfields) };
        next = heap.native_frame_with(r.nfields, raw, |i| if i == 0 { link } else { Value::from_raw(unsafe { *r.fields.add(i) }) });
        if outermost == Value::FALSE {
            outermost = next;
        }
    }
    (Pos::new(next, recs.first().map_or(tail.pc, |r| r.pc)), outermost)
}

/// How many words of frames `frames` (regions) hold.
fn region_words(frames: &[(u64, u64)]) -> u64 {
    frames.iter().map(|&(lo, hi)| (hi - lo) / 8).sum()
}

/// Continuation `k` given `v`: its frames put back, and the state told to
/// resume where it was taken. A whole one replaces this run's frames (its
/// last returning where this run's outermost does) and ends the regions
/// entered since it was taken; a delimited one goes on top of the
/// continuation procedure's caller (the frame that procedure made is
/// where), its last frame returning to that caller: on the stack if it
/// fits, as it mostly does; else the caller's frames copied onto the chain,
/// and a copy of `k`'s onto them.
///
/// A continuation with another machine's inside it (`capture_foreign`):
/// once its frames are back, that one is called with `v`, as what is not
/// native code, from them, where they called it, and they resume with
/// what it returns.
fn reinstate(rt: &mut fixpt_runtime::Runtime, st: &mut DState, k: Value, v: Value) -> u64 {
    if !rt.heap.take_shot(k) {
        return failed(st, fixpt_heap::ONE_SHOT_TWICE.into());
    }
    let data = rt.heap.bloblet_slot(k, CLOSURE_FREE0);
    // A whole continuation is given its value by the bottom machine: from
    // a run another machine called, it is thrown out to it.
    if rt.heap.obj_ref(data, 5) == Value::TRUE && fixpt_runtime::crossing::crossed() {
        THROWN.with(|t| t.set(Some((k, v))));
        return failed(st, "a whole continuation thrown out to the machine at the bottom".into());
    }
    let inner = rt.heap.obj_ref(data, fixpt_heap::NATIVE_CONT_INNER);
    let out = put_continuation(rt, st, k, v);
    if inner == Value::FALSE || st.trap != 0 {
        return out;
    }
    // The frames it put back are the call-out's; or, none (a whole one of
    // no frames, which returns from the run), none: the stack's top, past
    // which no frame is walked.
    (st.fp, st.native_sp) = if st.resume_pc == st.bottom_ret && st.resume_sp == st.stack_top {
        (st.stack_top + R_LINK, st.stack_top)
    } else {
        (st.resume_fp, st.resume_sp)
    };
    let x = call_foreign(rt, st, inner, &[v], Some(st.resume_pc));
    if st.trap == 0 {
        // Back with an abort to a prompt in these frames, which is where
        // the state now says to resume.
        if st.foreign_resume != 0 {
            st.foreign_resume = 0;
        } else {
            st.resume_x0 = x;
        }
    }
    0
}

/// `reinstate`'s frames put back, and where they resume.
fn put_continuation(rt: &mut fixpt_runtime::Runtime, st: &mut DState, k: Value, v: Value) -> u64 {
    let heap = &mut rt.heap;
    let data = heap.bloblet_slot(k, CLOSURE_FREE0);
    let ((kp, kwords), regions, whole) = (continuation_pos(heap, data), heap.obj_ref(data, 4), heap.obj_ref(data, 5) == Value::TRUE);
    let (to, chain) = if whole {
        heap.regions_exit_to(regions.as_fixnum() as usize);
        // Of no frames: the run returns `v`, as its outermost frame would.
        if kp.frame == Value::FALSE {
            set_cont(st, END, 0);
            (st.resume_sp, st.resume_fp, st.resume_pc, st.resume_x0) = (st.stack_top, st.bottom_link, st.bottom_ret, v.raw());
            return 0;
        }
        (kp, kwords)
    } else {
        let (link, ret) = (word(st.fp), word(st.fp + 8));
        // Its words, then, if they fit, its frames, with no list made.
        let (mut words, mut q) = (0u64, kp);
        while let Some((r, nq)) = step(heap, q) {
            words += r.n as u64;
            q = nq;
        }
        // In the place of the continuation procedure's frame, a stub's.
        let end = st.fp - R_LINK + STUB_FRAME;
        let base = end - 8 * words;
        if base >= st.stack_limit {
            let (mut lo, mut q) = (base, kp);
            while let Some((r, nq)) = step(heap, q) {
                let next = lo + 8 * r.n as u64;
                let last = next == end;
                put_frame(r, lo, if last { link } else { next + R_LINK }, if last && r.returns() { ret } else { r.w8 });
                st.stats.frames_restored += 1;
                (lo, q) = (next, nq);
            }
            (st.resume_sp, st.resume_fp, st.resume_pc, st.resume_x0) = (base, base + R_LINK, kp.pc, v.raw());
            return 0;
        }
        let recs: Vec<(Rec, bool)> = records(heap, kp).into_iter().map(|r| (r, r.returns())).collect();
        let below: Vec<(u64, u64)> = if link > st.fp && link - R_LINK < st.stack_top { frames_from(link, st.stack_top).collect() } else { Vec::new() };
        let rest = if below.is_empty() {
            cont_pos(st)
        } else {
            let last = outermost_second(st, below.last().expect("a frame").0);
            let mut p = heap_frames(heap, &below, last, cont_pos(st));
            p.pc = ret;
            p
        };
        let rest_words = region_words(&below) + st.cont_words;
        // `k`'s last returns where the caller resumes.
        let (mut p, outermost) = copy_records(heap, &recs.iter().map(|r| r.0).collect::<Vec<_>>(), rest);
        if outermost != Value::FALSE {
            heap.obj_set(outermost, 1, Value::fixnum(rest.pc as i64));
        }
        p.pc = kp.pc;
        (p, words + rest_words)
    };
    match restore(heap, st, to, chain) {
        Ok((lo, pc)) => {
            (st.resume_sp, st.resume_fp, st.resume_pc, st.resume_x0) = (lo, lo + R_LINK, pc, v.raw());
            0
        }
        Err(why) => failed(st, why),
    }
}

/// The marks for `key` in this run, innermost first: on the stack, then in
/// the chain.
fn run_marks(heap: &Heap, st: &DState, key: Value) -> Vec<Value> {
    let mut out: Vec<Value> = frames(st).filter(|&(fp, end)| is_control(fp, end, MARK_MARK, key)).map(|(lo, _)| Value::from_raw(word(lo + R_HEAD + 16))).collect();
    out.extend(chain_marks(heap, cont_pos(st), key));
    out
}

/// The marks for `key` in this run, then in the frames of the machines out
/// from it, if a machine called it (`fixpt_runtime::crossing`).
fn all_marks(rt: &mut fixpt_runtime::Runtime, st: &DState, key: Value) -> Vec<Value> {
    let mut out = run_marks(&rt.heap, st, key);
    out.extend(fixpt_runtime::crossing::marks(rt, key));
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
        // The marks of the continuation inside it first (`reinstate`).
        let inner = heap.obj_ref(data, fixpt_heap::NATIVE_CONT_INNER);
        let mut out = if inner != Value::FALSE { marks_of(heap, inner, key)? } else { Vec::new() };
        out.extend(chain_marks(heap, continuation_pos(heap, data).0, key));
        return Some(out);
    }
    let c = heap.continuation_of(k)?;
    let rs = heap.bloblet_slot(c, fixpt_heap::layout::cellular::CONT_RS);
    let entries: Vec<Value> = (0..heap.obj_len(rs)).map(|i| heap.obj_ref(rs, i)).collect();
    let inner = heap.bloblet_slot(c, fixpt_heap::layout::cellular::CONT_INNER);
    let mut out = if inner != Value::FALSE { marks_of(heap, inner, key)? } else { Vec::new() };
    let mut i = entries.len();
    while i >= 4 {
        i -= 4;
        if entries[i] == fixpt_engine::cellular::MARK_MARK && entries[i + 1] == key {
            out.push(entries[i + 2]);
        }
    }
    Some(out)
}

/// The words of the frame whose region is `lo` to `hi` that a collection
/// traces, as runs (where each starts, and how many words). A stub's frame
/// has none. A procedure's frame has its stack map after its link and
/// return address (`frame_shape`): the mask of its values, from the word
/// after the map, that are live; its raw words, after its values, never.
/// A control frame has its marker there instead, and its four words from
/// the marker on are values.
fn traced(lo: u64, hi: u64) -> Vec<(u64, usize)> {
    let (fields, mask) = frame_shape(lo, hi);
    if hi - lo <= STUB_FRAME {
        return Vec::new();
    }
    if !Value::from_raw(word(lo + R_HEAD)).is_fixnum() {
        return vec![(lo + R_HEAD, 4)];
    }
    // Its values, after the map: those the mask says (every one, too wide
    // for a map, cleared as it was made); never its raw words.
    let values = fields - 3;
    let mut runs: Vec<(u64, usize)> = Vec::new();
    for k in (0..values).filter(|&k| k + 1 >= 64 || mask & (1 << (k + 1)) != 0) {
        let at = lo + R_HEAD + 8 + 8 * k as u64;
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
    let c = heap.make_bloblet(const { fixpt_heap::layout::kind("native-closure") }, free.len() + 1, 0, true);
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
    if !closure.is_bloblet() || heap.bloblet_kind(closure) != const { fixpt_heap::layout::kind("native-closure") } {
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
        let lines = code_lines(&heap.bloblet_bytes(code));
        let _ = writeln!(out, "\ncode {}, {} instructions:", seen.len(), lines.len());
        for l in lines {
            let _ = writeln!(out, "  {l}");
        }
        // What it calls, and makes closures of: code in its fields, and
        // in the closures there.
        for k in 1..=heap.bloblet_head(code).fields {
            let f = heap.bloblet_slot(code, k);
            if heap.is_code_bloblet(f) {
                todo.push(f);
            } else if f.is_bloblet() && heap.bloblet_kind(f) == const { fixpt_heap::layout::kind("native-closure") } {
                todo.push(heap.bloblet_slot(f, CLOSURE_WORD));
            }
        }
    }
    Some(out)
}


/// Code in bytes, an instruction to a line: arm64's numbered by
/// instruction, x86_64's by byte.
fn code_lines(bytes: &[u8]) -> Vec<String> {
    if X86 {
        return crate::x86_64::disasm::listing(bytes).lines().map(str::to_string).collect();
    }
    bytes
        .chunks_exact(4)
        .enumerate()
        .map(|(i, w)| format!("{i:>4}  {}", crate::arm64::disasm::disassemble(u32::from_le_bytes(w.try_into().expect("four bytes")), i as i64)))
        .collect()
}
