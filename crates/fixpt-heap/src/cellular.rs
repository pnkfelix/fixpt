//! Making cellular words (`layout::cellular`): the one place a word is
//! made, whoever asks — the Rust builder, a Scheme primitive, FX-26 code —
//! because the native machines run a word's cells without looking at them
//! twice, so every word must be checked as it is made.

use crate::layout::cellular::{KIND, PRIMITIVES, ROUTINE_DOCOL, ROUTINES, WORD_CELL0, WORD_ENTRY, WORD_NAME, WORD_TWIN, operands};
use crate::{Heap, Value};

impl Heap {
    /// A word of `cells`, run by `docol`, published with its fields frozen,
    /// or why `cells` cannot be one. A cell is a routine's number (1 to
    /// `PRIMITIVES - 1`) or a word; after a routine come its operands:
    ///
    /// * `lit`: anything;
    ///
    /// `Value::DEFAULT` in a cell, or as `closure`'s operand, stands for the
    /// word being made.
    ///
    /// * `branch`, `0branch`: a fixnum landing on a cell of this word that
    ///   is not an operand;
    /// * `slot`, `slot!`, `free`: a non-negative fixnum;
    /// * `global`, `global!`: a bloblet of kind `bloblet` with a field;
    /// * `closure`: a word, and a non-negative fixnum;
    /// * `call`, `tailcall`: a non-negative fixnum;
    /// * `prim`: two non-negative fixnums (the primitive is checked when it
    ///   is called, by the runtime, which knows them).
    ///
    /// Made in the code area's stubbed part, its suffix the stub that
    /// enters `foreign` (`docs/research/code-stubs.md`): so that native code
    /// calls a closure of it as it calls native code.
    pub fn make_cellular_word(&mut self, name: Value, cells: &[Value]) -> Result<Value, String> {
        self.make_word(name, cells, true)
    }

    /// The same, made in the heap, with no stub: for a word that is only
    /// run, never a closure's, made for one call (`call_value`).
    pub fn make_transient_word(&mut self, name: Value, cells: &[Value]) -> Result<Value, String> {
        self.make_word(name, cells, false)
    }

    fn make_word(&mut self, name: Value, cells: &[Value], stubbed: bool) -> Result<Value, String> {
        // Which cells begin an instruction: every branch must land on one.
        let mut starts = vec![false; cells.len() + 1];
        let mut branches = Vec::new();
        let mut last = "";
        let mut i = 0;
        while i < cells.len() {
            starts[i] = true;
            let c = cells[i];
            let r = if c.is_fixnum() {
                let n = c.as_fixnum();
                if n <= 0 || n as usize >= PRIMITIVES || n as u64 == ROUTINE_DOCOL {
                    return Err(format!("cell {i}: {n} is no routine"));
                }
                ROUTINES[n as usize].0
            } else if c == Value::DEFAULT || self.is_cellular_word(c) {
                ""
            } else {
                return Err(format!("cell {i}: neither a routine nor a word"));
            };
            let ops = operands(r);
            if i + ops >= cells.len() {
                return Err(format!("cell {i}: `{r}` needs {ops} operand(s)"));
            }
            last = r;
            let op = |j: usize| cells[i + 1 + j];
            let non_negative = |v: Value| v.is_fixnum() && v.as_fixnum() >= 0;
            match r {
                "branch" | "0branch" => {
                    if !op(0).is_fixnum() {
                        return Err(format!("cell {i}: a branch's offset is a fixnum"));
                    }
                    branches.push((i, i as i64 + 2 + op(0).as_fixnum()));
                }
                "prim" if !non_negative(op(0)) || !non_negative(op(1)) => {
                    return Err(format!("cell {i}: `{r}` takes two non-negative fixnums"));
                }
                "global" | "global!" if !self.is_global_cell(op(0)) => {
                    return Err(format!("cell {i}: a global is a bloblet with a field"));
                }
                "closure" | "nclosure" if !(op(0) == Value::DEFAULT || self.is_cellular_word(op(0))) || !non_negative(op(1)) => {
                    return Err(format!("cell {i}: a closure is of a word, over a count of values"));
                }
                "slot" | "slot!" | "free" | "call" | "tailcall" | "tcall" | "ttailcall" if !non_negative(op(0)) => {
                    return Err(format!("cell {i}: `{r}` takes a count"));
                }
                // Field 1 is the trailer, which no program reads.
                "field" if !(op(0).is_fixnum() && op(0).as_fixnum() >= 2) => {
                    return Err(format!("cell {i}: `field` takes a field number, 2 or more"));
                }
                _ => {}
            }
            i += 1 + ops;
        }
        for (at, to) in branches {
            if to < 0 || to as usize > cells.len() || !starts[to as usize] {
                return Err(format!("cell {at}: the branch lands on no instruction"));
            }
        }
        // Running past the last cell would take the header for a cell, so
        // the last instruction must be one that never falls through.
        if !matches!(last, "exit" | "halt" | "branch" | "tailcall" | "ttailcall" | "return" | "withmark-tail" | "resume" | "undefined") {
            return Err("a word must end with an instruction that does not fall through (`exit`, `return`, a tail call, …)".into());
        }
        let fields = WORD_CELL0 - 2 + cells.len();
        let w = if stubbed { self.make_stubbed_bloblet(KIND, fields, true) } else { self.make_bloblet(KIND, fields, 0, true) };
        self.set_bloblet_slot(w, WORD_ENTRY, Value::fixnum(ROUTINE_DOCOL as i64));
        self.set_bloblet_slot(w, WORD_NAME, name);
        self.set_bloblet_slot(w, WORD_TWIN, Value::FALSE);
        // `Value::DEFAULT`, never a value a program has, stands for the
        // word itself, which did not exist to be named.
        for (i, c) in cells.iter().enumerate() {
            self.set_bloblet_slot(w, WORD_CELL0 + i, if *c == Value::DEFAULT { w } else { *c });
        }
        self.freeze_bloblet(w, true, false);
        Ok(w)
    }

    /// The word of `cells` named `name`, made once and kept in a global of
    /// its own: for a word the runtime makes again and again alike (a
    /// continuation's closure's, an adapter's), so that it is made once in
    /// the code area, not at every use.
    pub fn shared_word(&mut self, name: &str, cells: &[Value]) -> Value {
        let key = self.intern(&format!("%fx26-word:{name}"));
        let slot = self.symbol_global_slot(key);
        let held = self.global(slot);
        if self.is_cellular_word(held) {
            return held;
        }
        let name = self.intern(name);
        let w = self.make_cellular_word(name, cells).expect("a well-formed word");
        self.set_global(slot, w);
        w
    }

    /// A global's cell: a plain bloblet with its value in field 2.
    fn is_global_cell(&self, g: Value) -> bool {
        g.is_bloblet() && self.bloblet_kind(g) == crate::layout::kind("bloblet") && self.bloblet_head(g).fields >= 2
    }

    /// A continuation as a closure, so that everything callable is one: over
    /// `k`, running the word `slot 0; free 0; resume`. Allocates; does not
    /// collect.
    pub fn continuation_closure(&mut self, k: Value) -> Value {
        use crate::layout::cellular::{routine, CLOSURE_FREE0, CLOSURE_WORD};
        let f = |n: u64| Value::fixnum(n as i64);
        let cells = [f(const { routine("slot") }), f(0), f(const { routine("free") }), f(0), f(const { routine("resume") })];
        let word = self.shared_word("continuation", &cells);
        let c = self.make_bloblet(crate::layout::kind("cellular-closure"), 2, 0, true);
        self.set_bloblet_slot(c, CLOSURE_WORD, word);
        self.set_bloblet_slot(c, CLOSURE_FREE0, k);
        c
    }

    /// The saved frames of the native continuation `v` is: a native closure
    /// over one vector, marked first with `NATIVE_CONT_MARK`, which only the
    /// native convention makes (`fixpt-native`): `NATIVE_CONT_LEN` values,
    /// another machine's continuation inside it at `NATIVE_CONT_INNER` (or
    /// `#f`), its `Shots` at `NATIVE_CONT_SHOTS`.
    pub fn native_continuation_of(&self, v: Value) -> Option<Value> {
        use crate::layout::cellular::{CLOSURE_FREE0, CLOSURE_WORD};
        if !(v.is_bloblet() && self.bloblet_kind(v) == crate::layout::kind("native-closure")) || self.bloblet_head(v).fields <= CLOSURE_WORD {
            return None;
        }
        let data = self.bloblet_slot(v, CLOSURE_FREE0);
        (self.obj_type(data) == Some(crate::ObjType::Vector) && self.obj_len(data) == NATIVE_CONT_LEN && self.obj_ref(data, 0) == NATIVE_CONT_MARK).then_some(data)
    }

    /// Where continuation `v`'s `Shots` are, whatever machine took it: a
    /// native one's element, or a cellular one's field.
    fn shots_at(&self, v: Value) -> Option<(Value, Option<usize>)> {
        if let Some(data) = self.native_continuation_of(v) {
            return Some((data, Some(NATIVE_CONT_SHOTS)));
        }
        self.continuation_of(v).map(|k| (k, None))
    }

    fn shots(&self, v: Value) -> Option<Shots> {
        let (at, i) = self.shots_at(v)?;
        Some(Shots::of(match i {
            Some(i) => self.obj_ref(at, i),
            None => self.bloblet_slot(at, crate::layout::cellular::CONT_SHOTS),
        }))
    }

    fn set_shots(&mut self, v: Value, s: Shots) {
        let Some((at, i)) = self.shots_at(v) else { return };
        match i {
            Some(i) => self.obj_set(at, i, s.value()),
            None => self.set_bloblet_slot(at, crate::layout::cellular::CONT_SHOTS, s.value()),
        }
    }

    /// Continuation `v`, just taken, made one-shot (`callone`).
    pub fn make_one_shot(&mut self, v: Value) {
        debug_assert!(self.shots_at(v).is_some(), "a continuation");
        self.set_shots(v, Shots::Once);
    }

    /// Continuation `v` about to be given a value: false if it is one-shot
    /// and was given one already, which is then the caller's error to raise
    /// (`ONE_SHOT_TWICE`); else true, and a one-shot one is spent.
    pub fn take_shot(&mut self, v: Value) -> bool {
        match self.shots(v) {
            Some(Shots::Spent) => false,
            Some(Shots::Once) => {
                self.set_shots(v, Shots::Spent);
                true
            }
            _ => true,
        }
    }

    /// The continuation `v` is, or wraps: a closure over exactly one
    /// continuation whose word ends in `resume`, which only
    /// `continuation_closure` makes.
    pub fn continuation_of(&self, v: Value) -> Option<Value> {
        use crate::layout::cellular::{routine, CLOSURE_FREE0, CLOSURE_WORD};
        // An adapter over one (`ncallcc`): the one it adapts.
        if let Some(inner) = self.adapted(v) {
            return self.continuation_of(inner);
        }
        let k = crate::layout::kind("cellular-continuation");
        if v.is_bloblet() && self.bloblet_kind(v) == k {
            return Some(v);
        }
        if !(v.is_bloblet() && self.bloblet_kind(v) == crate::layout::kind("cellular-closure")) || self.bloblet_head(v).fields != CLOSURE_FREE0 {
            return None;
        }
        let (word, x) = (self.bloblet_slot(v, CLOSURE_WORD), self.bloblet_slot(v, CLOSURE_FREE0));
        let fields = self.bloblet_head(word).fields;
        let last = self.bloblet_slot(word, fields);
        (x.is_bloblet() && self.bloblet_kind(x) == k && last == Value::fixnum(const { routine("resume") } as i64)).then_some(x)
    }

    /// A procedure not yet defined: a closure whose word traps when called
    /// (`undefined`). What a global's cell holds before its definition runs,
    /// which a checked program never sees.
    pub fn undefined_closure(&mut self) -> Value {
        use crate::layout::cellular::{routine, CLOSURE_WORD};
        let cells = [Value::fixnum(const { routine("undefined") } as i64)];
        let word = self.shared_word("undefined", &cells);
        let c = self.make_bloblet(crate::layout::kind("cellular-closure"), 1, 0, true);
        self.set_bloblet_slot(c, CLOSURE_WORD, word);
        c
    }

    pub fn is_cellular_word(&self, v: Value) -> bool {
        v.is_bloblet() && self.bloblet_kind(v) == KIND
    }
}

/// What a native continuation's data holds first: a value no program can
/// make (`UNBOUND` with a payload).
pub const NATIVE_CONT_MARK: Value = Value(Value::UNBOUND.raw() + (3 << 8));

/// How many times a continuation may be given a value (`TODO.md` §98): any
/// number; once, not yet given one; once, and given it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Shots {
    Many,
    Once,
    Spent,
}

impl Shots {
    pub fn value(self) -> Value {
        Value::fixnum(self as i64)
    }

    pub fn of(v: Value) -> Shots {
        match v.is_fixnum().then(|| v.as_fixnum()) {
            Some(1) => Shots::Once,
            Some(2) => Shots::Spent,
            _ => Shots::Many,
        }
    }
}

/// What a second resume of a one-shot continuation fails with.
pub const ONE_SHOT_TWICE: &str = "a one-shot continuation resumed twice";

/// A native continuation's data: its length, and where the continuation
/// inside it and its `Shots` are (`native_continuation_of`).
pub const NATIVE_CONT_LEN: usize = 8;
pub const NATIVE_CONT_INNER: usize = 6;
pub const NATIVE_CONT_SHOTS: usize = 7;
