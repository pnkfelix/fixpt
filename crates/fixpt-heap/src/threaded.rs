//! Making threaded words (`layout::threaded`): the one place a word is
//! made, whoever asks — the Rust builder, a Scheme primitive, FX-26 code —
//! because the native machines run a word's cells without looking at them
//! twice, so every word must be checked as it is made.

use crate::layout::threaded::{KIND, PRIMITIVES, ROUTINE_DOCOL, ROUTINES, WORD_CELL0, WORD_ENTRY, WORD_NAME, operands};
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
    pub fn make_threaded_word(&mut self, name: Value, cells: &[Value]) -> Result<Value, String> {
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
            } else if c == Value::DEFAULT || self.is_threaded_word(c) {
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
                "closure" if !(op(0) == Value::DEFAULT || self.is_threaded_word(op(0))) || !non_negative(op(1)) => {
                    return Err(format!("cell {i}: a closure is of a word, over a count of values"));
                }
                "slot" | "slot!" | "free" | "call" | "tailcall" | "tcall" | "ttailcall" if !non_negative(op(0)) => {
                    return Err(format!("cell {i}: `{r}` takes a count"));
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
        let w = self.make_bloblet(KIND, WORD_CELL0 - 2 + cells.len(), 0, true);
        self.set_bloblet_slot(w, WORD_ENTRY, Value::fixnum(ROUTINE_DOCOL as i64));
        self.set_bloblet_slot(w, WORD_NAME, name);
        // `Value::DEFAULT`, never a value a program has, stands for the
        // word itself, which did not exist to be named.
        for (i, c) in cells.iter().enumerate() {
            self.set_bloblet_slot(w, WORD_CELL0 + i, if *c == Value::DEFAULT { w } else { *c });
        }
        self.freeze_bloblet(w, true, false);
        Ok(w)
    }

    /// A global's cell: a plain bloblet with its value in field 2.
    fn is_global_cell(&self, g: Value) -> bool {
        g.is_bloblet() && self.bloblet_kind(g) == crate::layout::kind("bloblet") && self.bloblet_head(g).fields >= 2
    }

    /// A continuation as a closure, so that everything callable is one: over
    /// `k`, running the word `slot 0; free 0; resume`. Allocates; does not
    /// collect.
    pub fn continuation_closure(&mut self, k: Value) -> Value {
        use crate::layout::threaded::{routine, CLOSURE_FREE0, CLOSURE_WORD};
        let f = |n: u64| Value::fixnum(n as i64);
        let cells = [f(routine("slot")), f(0), f(routine("free")), f(0), f(routine("resume"))];
        let name = self.intern("continuation");
        let word = self.make_threaded_word(name, &cells).expect("a well-formed word");
        let c = self.make_bloblet(crate::layout::kind("threaded-closure"), 2, 0, true);
        self.set_bloblet_slot(c, CLOSURE_WORD, word);
        self.set_bloblet_slot(c, CLOSURE_FREE0, k);
        c
    }

    /// The continuation `v` is, or wraps: a closure over exactly one
    /// continuation whose word ends in `resume`, which only
    /// `continuation_closure` makes.
    pub fn continuation_of(&self, v: Value) -> Option<Value> {
        use crate::layout::threaded::{routine, CLOSURE_FREE0, CLOSURE_WORD};
        let k = crate::layout::kind("threaded-continuation");
        if v.is_bloblet() && self.bloblet_kind(v) == k {
            return Some(v);
        }
        if !(v.is_bloblet() && self.bloblet_kind(v) == crate::layout::kind("threaded-closure")) || self.bloblet_head(v).fields != CLOSURE_FREE0 {
            return None;
        }
        let (word, x) = (self.bloblet_slot(v, CLOSURE_WORD), self.bloblet_slot(v, CLOSURE_FREE0));
        let fields = self.bloblet_head(word).fields;
        let last = self.bloblet_slot(word, fields);
        (x.is_bloblet() && self.bloblet_kind(x) == k && last == Value::fixnum(routine("resume") as i64)).then_some(x)
    }

    /// A procedure not yet defined: a closure whose word traps when called
    /// (`undefined`). What a subroutine's cell or box holds before its value.
    pub fn undefined_closure(&mut self) -> Value {
        use crate::layout::threaded::{routine, CLOSURE_WORD};
        let cells = [Value::fixnum(routine("undefined") as i64)];
        let name = self.intern("undefined");
        let word = self.make_threaded_word(name, &cells).expect("a well-formed word");
        let c = self.make_bloblet(crate::layout::kind("threaded-closure"), 1, 0, true);
        self.set_bloblet_slot(c, CLOSURE_WORD, word);
        c
    }

    pub fn is_threaded_word(&self, v: Value) -> bool {
        v.is_bloblet() && self.bloblet_kind(v) == KIND
    }
}
