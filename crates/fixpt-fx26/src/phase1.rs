//! Phase 1 (`docs/research/typed-macros.md`, "Decided: transformers in
//! the front end's heap", decision 2, stage 3): a namespace in a session's
//! runtime, made anew for each program's expansion, that a procedural
//! macro's transformer is defined in where its macro is defined, and called
//! in on each use's datum.
//!
//! It is a front end of its own, the conductor's `make-session-compiler`'s,
//! as a session's on the checker written in FX-26 is (`sessions26.rs`):
//! its checker holds the namespace's definitions as the REPL's holds a
//! program's, the standard environment's and the transformers' prelude's
//! first, and nothing of phase 0; its compiler's globals are the
//! namespace's, apart from the program's and every other namespace's. Its
//! code is cellular words, whatever the program's machine, run on the
//! cellular machine written in Rust, which every session's runtime has
//! (`Fx26Session::with_backend_preloaded_in`): as the transformers' session
//! runs them, so that both agree.
//!
//! The front end is held by a global of the namespace's own (`%phase1:N`),
//! which a collection updates; [`Phase1::end`] lets it go.

use crate::stage::Wrapped;
use fixpt_heap::Value;
use fixpt_runtime::Runtime;

/// The conductor's entry that makes the front end, and the fields of what
/// it makes, from 1: a step, and a name's global.
const MAKE: &str = "fx26-native:make-session-compiler";
const E_STEP: usize = 4;
const E_CELL: usize = 9;

/// How `session-step` checks: the first, in the standard environment, only
/// checked; and more, kept and compiled.
const FIRST: i64 = 0;
const MORE: i64 = 1;

/// What every transformer sees besides the standard environment.
const PRELUDE: &str = include_str!("macros/procedural-prelude.fx");

thread_local! {
    /// The namespaces made on this thread: each one's global its own.
    static MADE: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// A phase-1 namespace ([`self`]): the name of the global that holds its
/// front end.
pub struct Phase1 {
    global: String,
}

impl Phase1 {
    /// A namespace made in `rt`, the standard environment and the
    /// transformers' prelude defined in it; or why not (a session whose
    /// front end is not compiled, which `stage` cannot use either).
    pub fn new(rt: &mut Runtime) -> Result<Phase1, String> {
        let make = crate::stage::global(rt, MAKE).ok_or("phase 1 needs the front end compiled")?;
        let fe = fixpt_runtime::prim::call_front_end(rt, make, &[])?;
        let n = MADE.with(|m| m.replace(m.get() + 1));
        let p = Phase1 { global: format!("%phase1:{n}") };
        let sym = rt.heap.intern(&p.global);
        let slot = rt.heap.symbol_global_slot(sym);
        rt.heap.set_global(slot, fe);
        // The first step begins the checker in the standard environment, and
        // only checks; the prelude is the next, compiled.
        p.run(rt, "(define %phase1 unit #u)\n", FIRST).map_err(|e| format!("phase 1's start: {e}"))?;
        p.run(rt, PRELUDE, MORE).map_err(|e| format!("phase 1's prelude: {e}"))?;
        Ok(p)
    }

    /// `(define name ty code)` checked, compiled and run in the namespace;
    /// or why not, as its checker or compiler says it. Naming a global reads
    /// it, as in a program (`Checker::globals_effects`): a transformer of a
    /// type with no such effect binds the prelude's procedures it calls
    /// around its `lambda`, read as it is defined (`procedural::helpers`).
    pub fn define(&self, rt: &mut Runtime, name: &str, ty: &str, code: &str) -> Result<(), String> {
        self.run(rt, &format!("(define {name} {ty}\n{code})\n"), MORE)
    }

    /// The value of the namespace's global `name`, if it has one.
    pub fn value(&self, rt: &mut Runtime, name: &str) -> Option<Value> {
        let sym = rt.heap.intern(name);
        let cells = self.call_entry(rt, E_CELL, &[sym]).ok()?;
        (cells != Value::NULL).then(|| rt.heap.bloblet_slot(rt.heap.car(cells), fixpt_heap::layout::cellular::GLOBAL_VALUE))
    }

    /// The namespace's procedure `name` called with `args`, each rooted by
    /// the caller: its value, or why it failed.
    pub fn call(&self, rt: &mut Runtime, name: &str, args: &[Value]) -> Result<Value, String> {
        let base = rt.heap.root_count();
        for &a in args {
            rt.heap.push_root(a);
        }
        let f = self.value(rt, name);
        let args: Vec<Value> = (0..args.len()).map(|i| rt.heap.root_at(base + i)).collect();
        rt.heap.pop_roots_to(base);
        let f = f.ok_or_else(|| format!("phase 1 has no `{name}`"))?;
        on_cellular(rt, |rt| fixpt_runtime::prim::enter_word(rt, f, &args))
    }

    /// The namespace let go: its front end, and what it defined, garbage.
    pub fn end(self, rt: &mut Runtime) {
        let sym = rt.heap.intern(&self.global);
        let slot = rt.heap.symbol_global_slot(sym);
        rt.heap.set_global(slot, Value::FALSE);
    }

    fn front_end(&self, rt: &mut Runtime) -> Value {
        let sym = rt.heap.intern(&self.global);
        rt.heap.global(rt.heap.symbol_global_slot(sym))
    }

    /// Entry `i` of the namespace's front end, called with `args`.
    fn call_entry(&self, rt: &mut Runtime, i: usize, args: &[Value]) -> Result<Value, String> {
        let fe = self.front_end(rt);
        let f = rt.heap.product_field(fe, i);
        let fuel = std::mem::replace(&mut rt.word_fuel, u64::MAX);
        let out = fixpt_runtime::prim::call_front_end(rt, f, args);
        rt.word_fuel = fuel;
        out
    }

    /// `text`, definitions, checked as `how` says and kept, compiled, and
    /// the word run; or the refusal's message.
    fn run(&self, rt: &mut Runtime, text: &str, how: i64) -> Result<(), String> {
        let standard = crate::stage::standard(rt).ok_or("phase 1 needs the standard environment read")?;
        let w = Wrapped::of(String::new(), text, "", text, 0);
        let mark = rt.heap.push_root(standard);
        let whole = rt.heap.make_string(&w.whole);
        rt.heap.push_root(whole);
        let none = rt.heap.intern("%none");
        rt.heap.push_root(none);
        let rep = rt.heap.make_bytevector(&[]);
        rt.heap.push_root(rep);
        let [standard, whole, none, rep] = [0, 1, 2, 3].map(|i| rt.heap.root_at(mark + i));
        rt.heap.pop_roots_to(mark);
        // Made and not deferred; cellular words, neither native nor with
        // register code; no names given types by rep.
        let (made, deferred, native, registers) = (Value::TRUE, Value::FALSE, Value::FALSE, Value::FALSE);
        let mode = Value::fixnum(crate::ids::mode() as i64);
        let args = [standard, whole, Value::fixnum(w.skip), Value::fixnum(w.len), Value::fixnum(how), none, made, deferred, native, registers, rep, Value::NULL, mode];
        let out = self.call_entry(rt, E_STEP, &args)?;
        let tag = rt.heap.symbol_name(rt.heap.sum_tag(out));
        let payload = rt.heap.sum_payload(out);
        if tag == "checked" && how == FIRST {
            return Ok(());
        }
        if tag != "made" {
            // `(sum failed (product kind message start end))`.
            let message = rt.heap.product_field(payload, 2);
            return Err(if rt.heap.is_a(message, fixpt_heap::ObjType::String) { rt.heap.string_to_rust(message) } else { tag });
        }
        on_cellular(rt, |rt| fixpt_engine::cellular::run_word(rt, payload, &[])).map(|_| ())
    }
}

/// `f`, with the cellular machine written in Rust the runtime's: phase 1's
/// code is cellular words whatever machine runs the program's.
fn on_cellular<T>(rt: &mut Runtime, f: impl FnOnce(&mut Runtime) -> T) -> T {
    let run = std::mem::replace(&mut rt.run_word, Some(fixpt_engine::cellular::run_word));
    let out = f(rt);
    rt.run_word = run;
    out
}
