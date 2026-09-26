//! Threaded code: Forth's execution model over bloblets, and the Rust
//! bootstrap inner interpreter that runs it.
//!
//! A threaded word is a bloblet whose fields are its program (the layout is
//! `layout::threaded`). This interpreter reads words directly from the heap
//! and is the oracle for the native inner interpreter in `fixpt-native`,
//! which runs the same words. Both keep the same machine: a data stack of
//! Values, and a return stack of `(word, fixnum k)` pairs, so both stacks are
//! roots as they stand.
//!
//! Every word is published with its fields frozen, and the builder checks
//! each cell, so a cell is always a primitive's number or a word. The native
//! machine relies on that: it runs a cell without looking at it twice.

use fixpt_heap::layout::threaded::{KIND, PRIMITIVES, ROUTINE_DOCOL, ROUTINES, WORD_CELL0, WORD_ENTRY, WORD_NAME, routine};
use fixpt_heap::{Heap, Value};

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
    /// that cannot be written.
    Field { routine: &'static str },
    /// A word's entry, or an executed fixnum, is no routine.
    NoRoutine(i64),
    /// `execute` was given something that is neither a word nor a primitive.
    NotAWord,
    /// The machine's fuel ran out: a program ran longer than it was allowed.
    OutOfFuel,
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

    /// Push `x` when run.
    pub fn lit(&mut self, x: Value) -> &mut Self {
        self.prim("lit");
        self.cells.push(Pending::Value(x));
        self
    }

    /// Run `word`, which must be a threaded word.
    pub fn call(&mut self, heap: &Heap, word: Value) -> &mut Self {
        assert!(is_word(heap, word), "{word:?} is not a threaded word");
        self.cells.push(Pending::Value(word));
        self
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

    /// The word, published with its fields frozen.
    pub fn build(&self, heap: &mut Heap, name: &str) -> Value {
        let name = heap.intern(name);
        let n = self.cells.len();
        let w = heap.make_bloblet(KIND, WORD_CELL0 - 2 + n, 0, true);
        heap.set_bloblet_slot(w, WORD_ENTRY, Value::fixnum(ROUTINE_DOCOL as i64));
        heap.set_bloblet_slot(w, WORD_NAME, name);
        for (i, c) in self.cells.iter().enumerate() {
            let v = match c {
                Pending::Value(v) => *v,
                Pending::Recurse => w,
                Pending::To(l) => {
                    let to = self.labels[*l].expect("label never placed");
                    // Counted from the cell after the offset.
                    Value::fixnum(to as i64 - (i as i64 + 1))
                }
            };
            heap.set_bloblet_slot(w, WORD_CELL0 + i, v);
        }
        heap.freeze_bloblet(w, true, false);
        w
    }
}

/// A word whose entry is primitive `name`: the way to pass a primitive to
/// something that wants a word.
pub fn primitive_word(heap: &mut Heap, name: &str) -> Value {
    let sym = heap.intern(name);
    let w = heap.make_bloblet(KIND, WORD_CELL0 - 2, 0, true);
    heap.set_bloblet_slot(w, WORD_ENTRY, Value::fixnum(routine(name) as i64));
    heap.set_bloblet_slot(w, WORD_NAME, sym);
    heap.freeze_bloblet(w, true, false);
    w
}

pub fn is_word(heap: &Heap, v: Value) -> bool {
    v.is_bloblet() && heap.bloblet_kind(v) == KIND
}

pub fn word_name(heap: &Heap, w: Value) -> Value {
    heap.bloblet_slot(w, WORD_NAME)
}

// --------------------------------------------------------------- running

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

    /// Run `word` on the data stack as it stands, until it returns.
    pub fn run(&mut self, heap: &mut Heap, word: Value) -> Result<(), Trap> {
        let base = self.rs.len();
        let mut cur = Value::FALSE;
        let mut k = 0usize;
        if let Some((c, kk)) = self.enter(heap, word, &mut cur, k)? {
            (cur, k) = (c, kk);
        } else {
            return Ok(());
        }
        loop {
            let cell = heap.bloblet_slot(cur, k);
            k += 1;
            self.steps += 1;
            if self.fuel == 0 {
                return Err(Trap::OutOfFuel);
            }
            self.fuel -= 1;
            if cell.is_fixnum() {
                match self.prim(heap, cell.as_fixnum(), &mut cur, &mut k)? {
                    Flow::Next => {}
                    Flow::Exit => {
                        if self.rs.len() == base {
                            return Ok(());
                        }
                        let kk = self.rs.pop().expect("paired");
                        cur = self.rs.pop().expect("paired");
                        k = kk.as_fixnum() as usize;
                    }
                    Flow::Halt => return Ok(()),
                }
            } else if let Some((c, kk)) = self.enter(heap, cell, &mut cur, k)? {
                (cur, k) = (c, kk);
            }
        }
    }

    /// Run a word as a call from `(cur, k)`: push the return pair and enter
    /// it if it is made of cells, or run its routine.
    fn enter(&mut self, heap: &mut Heap, w: Value, cur: &mut Value, k: usize) -> Result<Option<(Value, usize)>, Trap> {
        let entry = heap.bloblet_slot(w, WORD_ENTRY).as_fixnum();
        if entry as u64 == ROUTINE_DOCOL {
            if cur.is_bloblet() {
                self.rs.push(*cur);
                self.rs.push(Value::fixnum(k as i64));
            }
            return Ok(Some((w, WORD_CELL0)));
        }
        let mut kk = k;
        match self.prim(heap, entry, cur, &mut kk)? {
            Flow::Next => Ok(None),
            Flow::Exit | Flow::Halt => Err(Trap::NoRoutine(entry)),
        }
    }

    fn pop(&mut self, routine: &'static str) -> Result<Value, Trap> {
        self.ds.pop().ok_or(Trap::Underflow { routine })
    }

    fn fix(&mut self, routine: &'static str) -> Result<i64, Trap> {
        let v = self.pop(routine)?;
        if v.is_fixnum() { Ok(v.as_fixnum()) } else { Err(Trap::Type { routine }) }
    }

    fn prim(&mut self, heap: &mut Heap, n: i64, cur: &mut Value, k: &mut usize) -> Result<Flow, Trap> {
        if n < 0 || n as usize >= PRIMITIVES || n as u64 == ROUTINE_DOCOL {
            return Err(Trap::NoRoutine(n));
        }
        let name = ROUTINES[n as usize].0;
        match n {
            EXIT => return Ok(Flow::Exit),
            HALT => return Ok(Flow::Halt),
            LIT => {
                self.ds.push(heap.bloblet_slot(*cur, *k));
                *k += 1;
            }
            BRANCH => {
                let off = heap.bloblet_slot(*cur, *k).as_fixnum();
                *k = (*k as i64 + 1 + off) as usize;
            }
            ZBRANCH => {
                let flag = self.pop(name)?;
                let off = heap.bloblet_slot(*cur, *k).as_fixnum();
                *k += 1;
                if flag == Value::FALSE {
                    *k = (*k as i64 + off) as usize;
                }
            }
            EXECUTE => {
                let w = self.pop(name)?;
                if w.is_fixnum() {
                    return self.prim(heap, w.as_fixnum(), cur, k);
                }
                if !is_word(heap, w) {
                    return Err(Trap::NotAWord);
                }
                if let Some((c, kk)) = self.enter(heap, w, cur, *k)? {
                    (*cur, *k) = (c, kk);
                }
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
                let n = self.ds.len();
                if n < 2 {
                    return Err(Trap::Underflow { routine: name });
                }
                self.ds.push(self.ds[n - 2]);
            }
            ADD | SUB | LESS => {
                let b = self.fix(name)?;
                let a = self.fix(name)?;
                let r = match n {
                    ADD => Value::try_fixnum(a + b).ok_or(Trap::Overflow { routine: name })?,
                    SUB => Value::try_fixnum(a - b).ok_or(Trap::Overflow { routine: name })?,
                    _ => Value::boolean(a < b),
                };
                self.ds.push(r);
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
                let v = heap.bloblet_field(obj, kf).map_err(|_| Trap::Field { routine: name })?;
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
                heap.set_bloblet_field(obj, kf, x).map_err(|_| Trap::Field { routine: name })?;
            }
            CONS => {
                if self.ds.len() < 2 {
                    return Err(Trap::Underflow { routine: name });
                }
                // A safepoint: everything live is on the two stacks or `cur`.
                let mut c = [*cur];
                heap.maybe_collect(&mut [&mut self.ds, &mut self.rs, &mut c]);
                *cur = c[0];
                let b = self.pop(name)?;
                let a = self.pop(name)?;
                let p = heap.cons(a, b);
                self.ds.push(p);
            }
            CAR | CDR => {
                let p = self.pop(name)?;
                if !p.is_pair() {
                    return Err(Trap::Type { routine: name });
                }
                self.ds.push(if n == CAR { heap.car(p) } else { heap.cdr(p) });
            }
            _ => return Err(Trap::NoRoutine(n)),
        }
        Ok(Flow::Next)
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
