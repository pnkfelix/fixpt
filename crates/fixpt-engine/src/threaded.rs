//! Threaded code: Forth's execution model over bloblets, and the Rust
//! bootstrap inner interpreter that runs it.
//!
//! A threaded word is a bloblet whose fields are its program (the layout is
//! `layout::threaded`). This interpreter reads words directly from the heap
//! and is the oracle for the native inner interpreters in `fixpt-native`,
//! which run the same words. The machine is a data stack of Values; a
//! frame pointer, where the running closure's frame (its arguments, then
//! its locals) begins on the data stack; the running closure, whose free
//! values are copied in (flat closures); and a return stack of
//! `(word, fixnum k, fixnum frame pointer, closure)` entries. Every one of
//! those is a Value, so both stacks are roots as they stand. The design
//! for code compiled from FX-26 follows the MacScheme machine's (Larceny's
//! `doc/LarcenyNotes/note13-malcode.html`), on a stack.
//!
//! Every word is made by `Heap::make_threaded_word`, which checks each cell
//! and operand, and published with its fields frozen, so a cell is always a
//! routine's number or a word. The native machines rely on that: they run a
//! cell without looking at it twice.

use fixpt_heap::layout::kind;
use fixpt_heap::layout::threaded::{
    CLOSURE_FREE0, CLOSURE_WORD, KIND, PRIMITIVES, ROUTINE_DOCOL, ROUTINES, WORD_CELL0, WORD_ENTRY, WORD_NAME, routine,
};
use fixpt_heap::{Heap, Value};
use fixpt_runtime::{PrimKind, Runtime};

/// The most values the data stack may hold, and the most calls the return
/// stack may hold, checked where a word is entered and where a branch is
/// taken. Between those points a word runs straight-line code, at most one
/// push per cell, so a machine needs only a word's worth of room beyond
/// these (`fixpt-native` leaves that much, then a guard).
pub const DS_LIMIT: usize = 1 << 17;
pub const RS_LIMIT: usize = 1 << 16;

/// A routine number as the fixnum a cell holds.
pub fn prim(name: &str) -> Value {
    Value::fixnum(routine(name) as i64)
}

/// Why a threaded program stopped short.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Trap {
    /// A primitive was given a value of the wrong kind.
    Type { routine: &'static str },
    /// A fixnum result would not fit.
    Overflow { routine: &'static str },
    /// A primitive needed more values than the data stack held.
    Underflow { routine: &'static str },
    /// `field@` or `field!` named a field the bloblet does not have, or one
    /// that cannot be written; or `slot` or `free` one that is not there.
    Field { routine: &'static str },
    /// A word's entry, or an executed fixnum, is no routine.
    NoRoutine(i64),
    /// `execute` was given something that is neither a word nor a primitive.
    NotAWord,
    /// The machine's fuel ran out: a program ran longer than it was allowed.
    OutOfFuel,
    /// More than `DS_LIMIT` values on the data stack.
    StackOverflow,
    /// More than `RS_LIMIT` calls deep.
    TooDeep,
    /// A runtime primitive failed, saying this; or there was no runtime to
    /// call it in.
    Prim(String),
}

impl Trap {
    /// A trap as the number the native machine reports it by, and back.
    pub fn code(&self) -> (u64, u64) {
        let r = |n: &str| routine(n);
        match self {
            Trap::Type { routine } => (1, r(routine)),
            Trap::Overflow { routine } => (2, r(routine)),
            Trap::Underflow { routine } => (3, r(routine)),
            Trap::Field { routine } => (4, r(routine)),
            Trap::NoRoutine(n) => (5, *n as u64),
            Trap::NotAWord => (6, 0),
            Trap::OutOfFuel => (7, 0),
            Trap::StackOverflow => (8, 0),
            Trap::TooDeep => (9, 0),
            Trap::Prim(_) => (10, 0),
        }
    }

    pub fn from_code(code: u64, aux: u64) -> Trap {
        let name = || ROUTINES.get(aux as usize).map(|r| r.0).unwrap_or("?");
        match code {
            1 => Trap::Type { routine: name() },
            2 => Trap::Overflow { routine: name() },
            3 => Trap::Underflow { routine: name() },
            4 => Trap::Field { routine: name() },
            5 => Trap::NoRoutine(aux as i64),
            7 => Trap::OutOfFuel,
            8 => Trap::StackOverflow,
            9 => Trap::TooDeep,
            10 => Trap::Prim("a runtime primitive failed".into()),
            _ => Trap::NotAWord,
        }
    }
}

// ------------------------------------------------------------------ building

enum Pending {
    Value(Value),
    Recurse,
    /// A branch offset, to a label.
    To(usize),
}

/// Builds one threaded word, cell by cell.
///
/// Values given to the builder must stay valid until [`WordBuilder::build`];
/// building allocates but never collects, so any Value live when building
/// starts is.
#[derive(Default)]
pub struct WordBuilder {
    cells: Vec<Pending>,
    labels: Vec<Option<usize>>,
}

/// A place in a word being built, to branch to.
#[derive(Copy, Clone)]
pub struct Label(usize);

impl WordBuilder {
    pub fn new() -> WordBuilder {
        WordBuilder::default()
    }

    /// A primitive, by name.
    pub fn prim(&mut self, name: &str) -> &mut Self {
        let n = routine(name);
        assert!(n != ROUTINE_DOCOL, "docol is an entry, not a cell");
        self.cells.push(Pending::Value(Value::fixnum(n as i64)));
        self
    }

    fn operand(&mut self, x: Value) -> &mut Self {
        self.cells.push(Pending::Value(x));
        self
    }

    /// Push `x` when run.
    pub fn lit(&mut self, x: Value) -> &mut Self {
        self.prim("lit").operand(x)
    }

    /// Run `word`, which must be a threaded word.
    pub fn call(&mut self, heap: &Heap, word: Value) -> &mut Self {
        assert!(is_word(heap, word), "{word:?} is not a threaded word");
        self.operand(word)
    }

    /// Push the word being built, as a value.
    pub fn lit_self(&mut self) -> &mut Self {
        self.prim("lit");
        self.cells.push(Pending::Recurse);
        self
    }

    /// Run the word being built.
    pub fn recurse(&mut self) -> &mut Self {
        self.cells.push(Pending::Recurse);
        self
    }

    pub fn label(&mut self) -> Label {
        self.labels.push(None);
        Label(self.labels.len() - 1)
    }

    /// The next cell is where `l` is.
    pub fn place(&mut self, l: Label) -> &mut Self {
        assert!(self.labels[l.0].is_none(), "label placed twice");
        self.labels[l.0] = Some(self.cells.len());
        self
    }

    pub fn branch(&mut self, l: Label) -> &mut Self {
        self.prim("branch");
        self.cells.push(Pending::To(l.0));
        self
    }

    /// Branch if the popped flag is `#f`.
    pub fn zbranch(&mut self, l: Label) -> &mut Self {
        self.prim("0branch");
        self.cells.push(Pending::To(l.0));
        self
    }

    /// Push slot `i` of this frame.
    pub fn slot(&mut self, i: usize) -> &mut Self {
        self.prim("slot").operand(Value::fixnum(i as i64))
    }

    pub fn slot_set(&mut self, i: usize) -> &mut Self {
        self.prim("slot!").operand(Value::fixnum(i as i64))
    }

    /// Push free value `i` of the closure running.
    pub fn free(&mut self, i: usize) -> &mut Self {
        self.prim("free").operand(Value::fixnum(i as i64))
    }

    /// Push what global `cell` (a one-field bloblet) holds.
    pub fn global(&mut self, cell: Value) -> &mut Self {
        self.prim("global").operand(cell)
    }

    pub fn global_set(&mut self, cell: Value) -> &mut Self {
        self.prim("global!").operand(cell)
    }

    /// Push `word` closed over the `n` values on top of the stack.
    pub fn closure(&mut self, word: Value, n: usize) -> &mut Self {
        self.prim("closure").operand(word).operand(Value::fixnum(n as i64))
    }

    /// Leave this frame, keeping the value on top, and return.
    pub fn ret(&mut self) -> &mut Self {
        self.prim("return")
    }

    /// Call the closure on top with the `n` values below it.
    pub fn call_closure(&mut self, n: usize) -> &mut Self {
        self.prim("call").operand(Value::fixnum(n as i64))
    }

    pub fn tailcall(&mut self, n: usize) -> &mut Self {
        self.prim("tailcall").operand(Value::fixnum(n as i64))
    }

    /// The runtime's primitive `name`, with `n` arguments.
    pub fn runtime(&mut self, name: &str, n: usize) -> &mut Self {
        let p = runtime_primitive(name).unwrap_or_else(|| panic!("no runtime primitive `{name}`"));
        self.prim("prim").operand(Value::fixnum(p as i64)).operand(Value::fixnum(n as i64))
    }

    /// The word, or why these cells cannot be one.
    pub fn try_build(&self, heap: &mut Heap, name: &str) -> Result<Value, String> {
        let name = heap.intern(name);
        let cells: Vec<Value> = self
            .cells
            .iter()
            .enumerate()
            .map(|(i, c)| match c {
                Pending::Value(v) => *v,
                Pending::Recurse => SELF,
                Pending::To(l) => {
                    let to = self.labels[*l].expect("label never placed");
                    // Counted from the cell after the offset.
                    Value::fixnum(to as i64 - (i as i64 + 1))
                }
            })
            .collect();
        heap.make_threaded_word(name, &cells)
    }

    /// The word, published with its fields frozen.
    pub fn build(&self, heap: &mut Heap, name: &str) -> Value {
        self.try_build(heap, name).unwrap_or_else(|e| panic!("`{name}` is no word: {e}"))
    }
}

/// In a word's cells as given to `make_threaded_word`: the word itself.
pub const SELF: Value = Value::DEFAULT;

/// A runtime primitive's number, for `prim`, if it is one the machine can
/// call: one that needs no engine.
pub fn runtime_primitive(name: &str) -> Option<usize> {
    fixpt_runtime::PRIMITIVES.iter().position(|p| p.name == name && matches!(p.kind, PrimKind::Simple(_)))
}

/// A word whose entry is primitive `name`: the way to pass a primitive to
/// something that wants a word.
pub fn primitive_word(heap: &mut Heap, name: &str) -> Value {
    assert!(routine(name) != ROUTINE_DOCOL, "docol runs cells, and this word has none");
    let sym = heap.intern(name);
    let w = heap.make_bloblet(KIND, WORD_CELL0 - 2, 0, true);
    heap.set_bloblet_slot(w, WORD_ENTRY, Value::fixnum(routine(name) as i64));
    heap.set_bloblet_slot(w, WORD_NAME, sym);
    heap.freeze_bloblet(w, true, false);
    w
}

pub fn is_word(heap: &Heap, v: Value) -> bool {
    heap.is_threaded_word(v)
}

pub fn word_name(heap: &Heap, w: Value) -> Value {
    heap.bloblet_slot(w, WORD_NAME)
}

// --------------------------------------------------------------- running

/// What the machine runs in: a heap alone, or a whole runtime, which the
/// `prim` routine needs.
enum Ctx<'a> {
    Heap(&'a mut Heap),
    Rt(&'a mut Runtime),
}

impl Ctx<'_> {
    fn heap(&mut self) -> &mut Heap {
        match self {
            Ctx::Heap(h) => h,
            Ctx::Rt(rt) => &mut rt.heap,
        }
    }
}

/// Where the machine is: the word, the next cell in it, where this frame
/// begins on the data stack, and the closure running (`#f` outside one).
struct Regs {
    cur: Value,
    k: usize,
    fp: usize,
    clo: Value,
}

/// The Rust inner interpreter's machine state.
pub struct Machine {
    pub ds: Vec<Value>,
    rs: Vec<Value>,
    /// Cells run, for measurement.
    pub steps: u64,
    /// Cells left to run before the machine traps with `OutOfFuel`, so that
    /// a program that runs away stops instead of hanging its host.
    pub fuel: u64,
}

impl Default for Machine {
    fn default() -> Machine {
        Machine { ds: Vec::new(), rs: Vec::new(), steps: 0, fuel: u64::MAX }
    }
}

impl Machine {
    pub fn new() -> Machine {
        Machine::default()
    }

    pub fn with_fuel(fuel: u64) -> Machine {
        Machine { fuel, ..Machine::default() }
    }

    /// Run `word` on the data stack as it stands, until it returns. With no
    /// runtime, `prim` traps.
    pub fn run(&mut self, heap: &mut Heap, word: Value) -> Result<(), Trap> {
        self.run_in(&mut Ctx::Heap(heap), word)
    }

    /// The same, in a runtime, whose primitives `prim` calls.
    pub fn run_in_runtime(&mut self, rt: &mut Runtime, word: Value) -> Result<(), Trap> {
        self.run_in(&mut Ctx::Rt(rt), word)
    }

    fn run_in(&mut self, cx: &mut Ctx, word: Value) -> Result<(), Trap> {
        let base = self.rs.len();
        let mut r = Regs { cur: Value::FALSE, k: 0, fp: self.ds.len(), clo: Value::FALSE };
        if !self.enter(cx, word, &mut r)? {
            return Ok(());
        }
        loop {
            let cell = cx.heap().bloblet_slot(r.cur, r.k);
            r.k += 1;
            self.steps += 1;
            if self.fuel == 0 {
                return Err(Trap::OutOfFuel);
            }
            self.fuel -= 1;
            if cell.is_fixnum() {
                match self.prim(cx, cell.as_fixnum(), &mut r)? {
                    Flow::Next => {}
                    Flow::Exit => {
                        if self.rs.len() == base {
                            return Ok(());
                        }
                        self.pop_return(&mut r);
                    }
                    Flow::Halt => return Ok(()),
                }
            } else {
                self.enter(cx, cell, &mut r)?;
            }
        }
    }

    fn push_return(&mut self, r: &Regs) {
        self.rs.push(r.cur);
        self.rs.push(Value::fixnum(r.k as i64));
        self.rs.push(Value::fixnum(r.fp as i64));
        self.rs.push(r.clo);
    }

    fn pop_return(&mut self, r: &mut Regs) {
        r.clo = self.rs.pop().expect("an entry");
        r.fp = self.rs.pop().expect("an entry").as_fixnum() as usize;
        r.k = self.rs.pop().expect("an entry").as_fixnum() as usize;
        r.cur = self.rs.pop().expect("an entry");
    }

    /// Run word `w` as a call from `r`: push the return entry and enter it
    /// if it is made of cells (and say so), or run its routine.
    fn enter(&mut self, cx: &mut Ctx, w: Value, r: &mut Regs) -> Result<bool, Trap> {
        let entry = cx.heap().bloblet_slot(w, WORD_ENTRY).as_fixnum();
        if entry as u64 == ROUTINE_DOCOL {
            self.check_limits()?;
            if r.cur.is_bloblet() {
                self.push_return(r);
            }
            (r.cur, r.k) = (w, WORD_CELL0);
            return Ok(true);
        }
        match self.prim(cx, entry, r)? {
            Flow::Next => Ok(false),
            Flow::Exit | Flow::Halt => Err(Trap::NoRoutine(entry)),
        }
    }

    fn check_limits(&self) -> Result<(), Trap> {
        if self.ds.len() > DS_LIMIT {
            return Err(Trap::StackOverflow);
        }
        if self.rs.len() / 4 >= RS_LIMIT {
            return Err(Trap::TooDeep);
        }
        Ok(())
    }

    fn pop(&mut self, routine: &'static str) -> Result<Value, Trap> {
        self.ds.pop().ok_or(Trap::Underflow { routine })
    }

    fn fix(&mut self, routine: &'static str) -> Result<i64, Trap> {
        let v = self.pop(routine)?;
        if v.is_fixnum() { Ok(v.as_fixnum()) } else { Err(Trap::Type { routine }) }
    }

    /// The operand in the next cell.
    fn operand(heap: &Heap, r: &mut Regs) -> Value {
        let v = heap.bloblet_slot(r.cur, r.k);
        r.k += 1;
        v
    }

    /// A safepoint: everything live is on the stacks or in `r`.
    fn safepoint(&mut self, heap: &mut Heap, r: &mut Regs) {
        let mut regs = [r.cur, r.clo];
        heap.maybe_collect(&mut [&mut self.ds, &mut self.rs, &mut regs]);
        (r.cur, r.clo) = (regs[0], regs[1]);
    }

    /// Call the closure on top of the stack with the `n` values below it,
    /// which become its frame; `tail` replaces this frame and call instead,
    /// sliding the new frame down over the old, so the stacks do not grow.
    /// No allocation: a call is stack work, as in the MacScheme machine.
    fn call(&mut self, cx: &mut Ctx, r: &mut Regs, n: usize, tail: bool, routine: &'static str) -> Result<(), Trap> {
        if self.ds.len() < r.fp + n + 1 {
            return Err(Trap::Underflow { routine });
        }
        let heap = cx.heap();
        let c = self.ds.pop().expect("counted");
        if !(c.is_bloblet() && heap.bloblet_kind(c) == kind("threaded-closure")) {
            return Err(Trap::Type { routine });
        }
        self.check_limits()?;
        let word = heap.bloblet_slot(c, CLOSURE_WORD);
        if tail {
            let from = self.ds.len() - n;
            self.ds.drain(r.fp..from);
        } else {
            self.push_return(r);
            r.fp = self.ds.len() - n;
        }
        (r.cur, r.k, r.clo) = (word, WORD_CELL0, c);
        Ok(())
    }

    fn prim(&mut self, cx: &mut Ctx, n: i64, r: &mut Regs) -> Result<Flow, Trap> {
        if n < 0 || n as usize >= PRIMITIVES || n as u64 == ROUTINE_DOCOL {
            return Err(Trap::NoRoutine(n));
        }
        let name = ROUTINES[n as usize].0;
        match n {
            EXIT => return Ok(Flow::Exit),
            HALT => return Ok(Flow::Halt),
            LIT => {
                let v = Self::operand(cx.heap(), r);
                self.ds.push(v);
            }
            BRANCH => {
                let off = Self::operand(cx.heap(), r).as_fixnum();
                r.k = (r.k as i64 + off) as usize;
                self.check_limits()?;
            }
            ZBRANCH => {
                let flag = self.pop(name)?;
                let off = Self::operand(cx.heap(), r).as_fixnum();
                if flag == Value::FALSE {
                    r.k = (r.k as i64 + off) as usize;
                    self.check_limits()?;
                }
            }
            EXECUTE => {
                let w = self.pop(name)?;
                if w.is_fixnum() {
                    return self.prim(cx, w.as_fixnum(), r);
                }
                if !is_word(cx.heap(), w) {
                    return Err(Trap::NotAWord);
                }
                self.enter(cx, w, r)?;
            }
            DUP => {
                let a = *self.ds.last().ok_or(Trap::Underflow { routine: name })?;
                self.ds.push(a);
            }
            DROP => {
                self.pop(name)?;
            }
            SWAP => {
                let b = self.pop(name)?;
                let a = self.pop(name)?;
                self.ds.push(b);
                self.ds.push(a);
            }
            OVER => {
                let len = self.ds.len();
                if len < 2 {
                    return Err(Trap::Underflow { routine: name });
                }
                self.ds.push(self.ds[len - 2]);
            }
            ADD | SUB | LESS => {
                let b = self.fix(name)?;
                let a = self.fix(name)?;
                let v = match n {
                    ADD => Value::try_fixnum(a + b).ok_or(Trap::Overflow { routine: name })?,
                    SUB => Value::try_fixnum(a - b).ok_or(Trap::Overflow { routine: name })?,
                    _ => Value::boolean(a < b),
                };
                self.ds.push(v);
            }
            EQ => {
                let b = self.pop(name)?;
                let a = self.pop(name)?;
                self.ds.push(Value::boolean(a == b));
            }
            FIELD_REF => {
                let kf = self.pop(name)?;
                let obj = self.pop(name)?;
                if !kf.is_fixnum() || !obj.is_bloblet() {
                    return Err(Trap::Type { routine: name });
                }
                let kf = usize::try_from(kf.as_fixnum()).map_err(|_| Trap::Field { routine: name })?;
                let v = cx.heap().bloblet_field(obj, kf).map_err(|_| Trap::Field { routine: name })?;
                self.ds.push(v);
            }
            FIELD_SET => {
                let kf = self.pop(name)?;
                let obj = self.pop(name)?;
                let x = self.pop(name)?;
                if !kf.is_fixnum() || !obj.is_bloblet() {
                    return Err(Trap::Type { routine: name });
                }
                let kf = usize::try_from(kf.as_fixnum()).map_err(|_| Trap::Field { routine: name })?;
                cx.heap().set_bloblet_field(obj, kf, x).map_err(|_| Trap::Field { routine: name })?;
            }
            CONS => {
                if self.ds.len() < 2 {
                    return Err(Trap::Underflow { routine: name });
                }
                self.safepoint(cx.heap(), r);
                let b = self.pop(name)?;
                let a = self.pop(name)?;
                let p = cx.heap().cons(a, b);
                self.ds.push(p);
            }
            CAR | CDR => {
                let p = self.pop(name)?;
                if !p.is_pair() {
                    return Err(Trap::Type { routine: name });
                }
                let heap = cx.heap();
                self.ds.push(if n == CAR { heap.car(p) } else { heap.cdr(p) });
            }
            SLOT => {
                let i = Self::operand(cx.heap(), r).as_fixnum() as usize;
                let v = *self.ds.get(r.fp + i).ok_or(Trap::Field { routine: name })?;
                self.ds.push(v);
            }
            SLOT_SET => {
                let i = Self::operand(cx.heap(), r).as_fixnum() as usize;
                let x = self.pop(name)?;
                *self.ds.get_mut(r.fp + i).ok_or(Trap::Field { routine: name })? = x;
            }
            FREE => {
                let heap = cx.heap();
                let i = Self::operand(heap, r).as_fixnum() as usize;
                if !r.clo.is_bloblet() {
                    return Err(Trap::Field { routine: name });
                }
                let v = heap.bloblet_field(r.clo, CLOSURE_FREE0 + i).map_err(|_| Trap::Field { routine: name })?;
                self.ds.push(v);
            }
            RETURN => {
                let v = self.pop(name)?;
                if self.ds.len() < r.fp {
                    return Err(Trap::Underflow { routine: name });
                }
                self.ds.truncate(r.fp);
                self.ds.push(v);
                return Ok(Flow::Exit);
            }
            GLOBAL => {
                let heap = cx.heap();
                let g = Self::operand(heap, r);
                let v = heap.bloblet_slot(g, 2);
                self.ds.push(v);
            }
            GLOBAL_SET => {
                let g = Self::operand(cx.heap(), r);
                let x = self.pop(name)?;
                cx.heap().set_bloblet_slot(g, 2, x);
            }
            CLOSURE => {
                self.safepoint(cx.heap(), r);
                let heap = cx.heap();
                let w = Self::operand(heap, r);
                let count = Self::operand(heap, r).as_fixnum() as usize;
                if self.ds.len() < r.fp + count {
                    return Err(Trap::Underflow { routine: name });
                }
                let c = heap.make_bloblet(kind("threaded-closure"), count + 1, 0, true);
                heap.set_bloblet_slot(c, CLOSURE_WORD, w);
                let free = self.ds.split_off(self.ds.len() - count);
                for (i, v) in free.into_iter().enumerate() {
                    heap.set_bloblet_slot(c, CLOSURE_FREE0 + i, v);
                }
                self.ds.push(c);
            }
            CALL | TAILCALL => {
                let count = Self::operand(cx.heap(), r).as_fixnum() as usize;
                self.call(cx, r, count, n == TAILCALL, name)?;
            }
            PRIM => {
                let p = Self::operand(cx.heap(), r).as_fixnum() as usize;
                let count = Self::operand(cx.heap(), r).as_fixnum() as usize;
                if self.ds.len() < count {
                    return Err(Trap::Underflow { routine: name });
                }
                let Ctx::Rt(rt) = cx else { return Err(Trap::Prim("no runtime to call a primitive in".into())) };
                let Some(def) = fixpt_runtime::PRIMITIVES.get(p) else { return Err(Trap::Prim(format!("no primitive {p}"))) };
                let PrimKind::Simple(f) = def.kind else { return Err(Trap::Prim(format!("`{}` needs an engine", def.name))) };
                if count < def.min || def.max.is_some_and(|m| count > m) {
                    return Err(Trap::Prim(format!("`{}` given {count} argument(s)", def.name)));
                }
                // A primitive may allocate, and allocation never collects
                // here, so this is a safepoint first.
                let mut regs = [r.cur, r.clo];
                rt.heap.maybe_collect(&mut [&mut self.ds, &mut self.rs, &mut regs]);
                (r.cur, r.clo) = (regs[0], regs[1]);
                let mut args = self.ds.split_off(self.ds.len() - count);
                match f(rt, &mut args) {
                    Ok(v) => self.ds.push(v),
                    Err(t) => return Err(Trap::Prim(describe(rt, t.obj))),
                }
            }
            _ => return Err(Trap::NoRoutine(n)),
        }
        Ok(Flow::Next)
    }
}

/// Run `word` with `args` on the data stack in `rt`: the value left on top.
/// What the runtime's `%run-word` calls (`Runtime::run_word`).
pub fn run_word(rt: &mut Runtime, word: Value, args: &[Value]) -> Result<Value, String> {
    let mut m = Machine::new();
    m.ds.extend_from_slice(args);
    m.run_in_runtime(rt, word).map_err(|t| format!("{t:?}"))?;
    m.ds.pop().ok_or_else(|| "the word left nothing".to_string())
}

/// A thrown value as a message.
fn describe(rt: &Runtime, obj: Value) -> String {
    if rt.is_error_object(obj) {
        fixpt_runtime::display_value(&rt.heap, rt.heap.obj_ref(obj, 1))
    } else {
        fixpt_runtime::write_value(&rt.heap, obj)
    }
}

const EXIT: i64 = routine("exit") as i64;
const HALT: i64 = routine("halt") as i64;
const LIT: i64 = routine("lit") as i64;
const BRANCH: i64 = routine("branch") as i64;
const ZBRANCH: i64 = routine("0branch") as i64;
const EXECUTE: i64 = routine("execute") as i64;
const DUP: i64 = routine("dup") as i64;
const DROP: i64 = routine("drop") as i64;
const SWAP: i64 = routine("swap") as i64;
const OVER: i64 = routine("over") as i64;
const EQ: i64 = routine("eq") as i64;
const FIELD_REF: i64 = routine("field@") as i64;
const FIELD_SET: i64 = routine("field!") as i64;
const CONS: i64 = routine("cons") as i64;
const ADD: i64 = routine("+") as i64;
const SUB: i64 = routine("-") as i64;
const LESS: i64 = routine("<") as i64;
const CAR: i64 = routine("car") as i64;
const CDR: i64 = routine("cdr") as i64;
const SLOT: i64 = routine("slot") as i64;
const SLOT_SET: i64 = routine("slot!") as i64;
const FREE: i64 = routine("free") as i64;
const RETURN: i64 = routine("return") as i64;
const GLOBAL: i64 = routine("global") as i64;
const GLOBAL_SET: i64 = routine("global!") as i64;
const CLOSURE: i64 = routine("closure") as i64;
const CALL: i64 = routine("call") as i64;
const TAILCALL: i64 = routine("tailcall") as i64;
const PRIM: i64 = routine("prim") as i64;

enum Flow {
    Next,
    Exit,
    Halt,
}

/// Small threaded programs, shared by the tests of both inner interpreters
/// and by their benchmark.
pub mod examples {
    use super::WordBuilder;
    use fixpt_heap::{Heap, Value};

    fn n(i: i64) -> Value {
        Value::fixnum(i)
    }

    /// `( n -- fib(n) )`, doubly recursive.
    pub fn fib(heap: &mut Heap) -> Value {
        let mut b = WordBuilder::new();
        let big = b.label();
        b.prim("dup").lit(n(2)).prim("<").zbranch(big).prim("exit");
        b.place(big);
        b.prim("dup").lit(n(1)).prim("-").recurse();
        b.prim("swap").lit(n(2)).prim("-").recurse();
        b.prim("+").prim("exit");
        b.build(heap, "fib")
    }

    /// `( acc n -- acc+n+(n-1)+…+1 )`, a loop.
    pub fn sum_to(heap: &mut Heap) -> Value {
        let mut b = WordBuilder::new();
        let (top, more) = (b.label(), b.label());
        b.place(top);
        b.prim("dup").lit(n(0)).prim("eq").zbranch(more).prim("drop").prim("exit");
        b.place(more);
        b.prim("swap").prim("over").prim("+").prim("swap").lit(n(1)).prim("-").branch(top);
        b.build(heap, "sum-to")
    }

    /// `( n -- (1 2 … n) )`, consing.
    pub fn iota(heap: &mut Heap) -> Value {
        let mut b = WordBuilder::new();
        let (top, more) = (b.label(), b.label());
        b.lit(Value::NULL).prim("swap");
        b.place(top);
        b.prim("dup").lit(n(0)).prim("eq").zbranch(more).prim("drop").prim("exit");
        b.place(more);
        b.prim("swap").prim("over").prim("swap").prim("cons").prim("swap").lit(n(1)).prim("-").branch(top);
        b.build(heap, "iota")
    }

    /// `( list -- sum )`, recursive, with `car` and `cdr`.
    pub fn list_sum(heap: &mut Heap) -> Value {
        let mut b = WordBuilder::new();
        let more = b.label();
        b.prim("dup").lit(Value::NULL).prim("eq").zbranch(more).prim("drop").lit(n(0)).prim("exit");
        b.place(more);
        b.prim("dup").prim("car").prim("swap").prim("cdr").recurse().prim("+").prim("exit");
        b.build(heap, "list-sum")
    }

    /// `( n -- sum(1..n) )` by way of a list: `iota` then `list-sum`,
    /// calling other words.
    pub fn sum_by_list(heap: &mut Heap) -> Value {
        let iota = iota(heap);
        let sum = list_sum(heap);
        let mut b = WordBuilder::new();
        b.call(heap, iota).call(heap, sum).prim("exit");
        b.build(heap, "sum-by-list")
    }
}
