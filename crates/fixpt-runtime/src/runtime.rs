//! Session-wide state: the heap, the interners, and the handful of well-known
//! objects the primitives need to reach.

use crate::error::{Outcome, Thrown};
use fixpt_heap::{Heap, ObjType, Value};
use fixpt_read::{Interner, SourceMap};

/// Where `display` and `write` go.
pub enum Sink {
    /// Straight to the process's standard output — the REPL.
    Stdout,
    /// Accumulated in a buffer — tests, and `with-output-to-string`.
    Buffer(String),
}

pub struct Runtime {
    pub heap: Heap,
    /// Compile-time symbol names. Distinct from the heap's symbol table, which
    /// holds runtime symbol *objects*; this one is unaffected by collection.
    pub interner: Interner,
    pub sources: SourceMap,
    pub out: Sink,
    /// Where `%open-input-file` resolves a relative path.
    pub file_base: std::path::PathBuf,

    /// Root index of the record type used for R7RS error objects. Held as a
    /// root index rather than a `Value` so it survives collection — and so it
    /// survives a heap image, since roots are dumped in order and indices stay
    /// valid.
    error_rtd_root: usize,

    /// How `%run-word` runs a cellular word: the cellular machine lives in
    /// `fixpt-engine`, above this crate, which installs it.
    pub run_word: Option<RunWord>,
    /// How that machine shows a word's machine code, or what stands for it
    /// (`,disassemble-asm`); none for a machine that has none.
    pub machine_code: Option<MachineCode>,
    /// Whether `%disassemble` shows it too.
    pub show_machine_code: bool,
    /// How a closure of code in the native convention is shown: its machine
    /// code (`fixpt-native`, above this crate, installs it).
    pub native_code: Option<MachineCode>,
    /// How a cellular machine calls a closure of code in the native
    /// convention (`fixpt-native` installs it): its value, or why it
    /// stopped. None: such a call is a type error.
    pub call_native: Option<CallNative>,
    /// How `%fx26-convert` makes an adapter (`fixpt-native` installs it):
    /// a procedure of the other convention that calls the one given.
    /// None: no procedure of the other convention can be made here.
    pub adapt: Option<Adapt>,
    /// How many steps (cells, or polls in machine code) a run of a word by
    /// `run_word` may take before it stops; unlimited unless set, as the
    /// FX-26 REPL sets it from its step limit for the run of a form.
    pub word_fuel: u64,
}

/// Run cellular word `word` with `args` on its data stack; its value, or
/// why it stopped.
pub type RunWord = fn(&mut Runtime, Value, &[Value]) -> Result<Value, String>;

/// Call native closure `closure` with `args`: its value, or how it left.
/// Every value the caller holds must be rooted, since the call may collect.
pub type CallNative = fn(&mut Runtime, Value, &[Value]) -> Result<Value, NativeExit>;

/// An adapter of procedure `f`, of `arity` arguments, to the native
/// convention if `native`, else to the cellular one: a procedure of that
/// convention that calls `f`; or why none could be made.
pub type Adapt = fn(&mut Runtime, Value, usize, bool) -> Result<Value, String>;

/// How a call between machines left, if not with a value.
#[derive(Debug)]
pub enum NativeExit {
    /// It stopped, for this reason.
    Failed(String),
    /// A whole continuation taken by the machine that called was given a
    /// value: the call's frames are gone, and that machine goes on from
    /// the continuation. Nothing has collected since, so the values are as
    /// they were.
    Throw { k: Value, v: Value },
    /// An abort to prompt tag `tag`, with value `v`, that found no prompt
    /// for it in the call: the call's frames are gone, and the machine
    /// that called goes on looking in its own.
    Abort { tag: Value, v: Value },
}

/// A word's machine code, shown, as the machine that runs it has it; or
/// none, if it has none for this word.
pub type MachineCode = fn(&fixpt_heap::Heap, Value) -> Option<String>;

/// Root 0 of any runtime's heap is the error-object record type.
///
/// Positional, and therefore a real invariant rather than a coincidence:
/// [`Runtime::new`] pushes it first, and [`Runtime::from_heap`] relies on that
/// to resume a heap loaded from an image.
pub const ERROR_RTD_ROOT: usize = 0;

impl Runtime {
    pub fn new() -> Runtime {
        let mut heap = Heap::new();
        let mut interner = Interner::new();
        interner.intern("error-object");

        // `[name:Symbol, field-names:Vector]`
        let name = heap.intern("error-object");
        let msg = heap.intern("message");
        let irritants = heap.intern("irritants");
        let fields = heap.vector_from(&[msg, irritants]);
        let rtd = heap.alloc(ObjType::RecordType, 2, Value::UNSPECIFIED);
        heap.obj_set(rtd, 0, name);
        heap.obj_set(rtd, 1, fields);
        let error_rtd_root = heap.push_root(rtd);
        debug_assert_eq!(error_rtd_root, ERROR_RTD_ROOT, "root order is part of the image format");

        Runtime {
            heap,
            interner,
            sources: SourceMap::new(),
            out: Sink::Stdout,
            file_base: std::path::PathBuf::from("."),
            error_rtd_root,
            run_word: None,
            machine_code: None,
            show_machine_code: false,
            native_code: None,
            call_native: None,
            adapt: None,
            word_fuel: u64::MAX,
        }
    }

    pub fn error_rtd(&self) -> Value {
        self.heap.root_at(self.error_rtd_root)
    }

    /// Build an R7RS error object: `[rtd, message:String, irritants:list]`.
    pub fn error_object(&mut self, message: &str, irritants: &[Value]) -> Value {
        let msg = self.heap.make_string(message);
        let irr = self.heap.list_from(irritants);
        let rtd = self.error_rtd();
        let obj = self.heap.alloc(ObjType::Record, 3, Value::UNSPECIFIED);
        self.heap.obj_set(obj, 0, rtd);
        self.heap.obj_set(obj, 1, msg);
        self.heap.obj_set(obj, 2, irr);
        obj
    }

    pub fn is_error_object(&self, v: Value) -> bool {
        self.heap.is_a(v, ObjType::Record)
            && self.heap.obj_len(v) == 3
            && self.heap.obj_ref(v, 0) == self.error_rtd()
    }

    /// Signal an error, as a primitive would.
    pub fn fail<T>(&mut self, message: &str, irritants: &[Value]) -> Outcome<T> {
        let obj = self.error_object(message, irritants);
        Err(Thrown::raise(obj))
    }

    /// The common shape: "`what` expected, got `v`".
    pub fn type_error<T>(&mut self, what: &str, v: Value) -> Outcome<T> {
        self.fail(&format!("expected {what}"), &[v])
    }

    // --------------------------------------------------------------- output
    pub fn emit(&mut self, s: &str) {
        match &mut self.out {
            Sink::Stdout => {
                use std::io::Write as _;
                let mut so = std::io::stdout().lock();
                let _ = so.write_all(s.as_bytes());
                let _ = so.flush();
            }
            Sink::Buffer(b) => b.push_str(s),
        }
    }

    /// Redirect output to a buffer and return the previous sink.
    pub fn capture(&mut self) -> Sink {
        std::mem::replace(&mut self.out, Sink::Buffer(String::new()))
    }
    pub fn restore(&mut self, sink: Sink) -> String {
        match std::mem::replace(&mut self.out, sink) {
            Sink::Buffer(b) => b,
            Sink::Stdout => String::new(),
        }
    }
}

impl Runtime {
    /// Resume a heap loaded from an image.
    ///
    /// The interner is *not* part of an image — it is compile-time state — so a
    /// resumed runtime starts with an empty one. That is enough to call the
    /// procedures the image already holds; expanding new source needs a fresh
    /// front end on top.
    pub fn from_heap(heap: fixpt_heap::Heap) -> Runtime {
        Runtime {
            heap,
            interner: Interner::new(),
            sources: SourceMap::new(),
            out: Sink::Stdout,
            file_base: std::path::PathBuf::from("."),
            error_rtd_root: ERROR_RTD_ROOT,
            run_word: None,
            machine_code: None,
            show_machine_code: false,
            native_code: None,
            call_native: None,
            adapt: None,
            word_fuel: u64::MAX,
        }
    }
}

impl Default for Runtime {
    fn default() -> Runtime {
        Runtime::new()
    }
}
