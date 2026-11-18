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
//! which a collection updates; [`Phase1::end`] lets it go. An expansion's
//! is the runtime's current one, `%phase1:current` ([`Phase1::current`]),
//! which both front ends' expanders call their transformers in
//! ([`run_transformer`]: the Rust expander's from inside its lending, the
//! one written in FX-26's by `%fx26-call-procedural`), each transformer
//! defined there once, by its style and text (`%phase1:current:defined`):
//! so that both run the one compiled closure, and agree by construction.

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

/// The global that holds the runtime's current namespace, an expansion's
/// (and, after it, `:DIGEST`, each of its namespaces of phase-1 forms).
const CURRENT: &str = "%phase1:current";
/// The global listing the expansion's namespaces of phase-1 forms.
const ALL: &str = "%phase1:current:all";

/// Phase-1 forms `forms`'s digest: what names their namespace.
pub(crate) fn forms_digest(forms: &[String]) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut h = std::collections::hash_map::DefaultHasher::new();
    forms.hash(&mut h);
    h.finish()
}

/// What every transformer sees besides the standard environment.
const PRELUDE: &str = include_str!("macros/procedural-prelude.fx");

thread_local! {
    /// The namespaces made on this thread: each one's global its own.
    static MADE: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    /// The expander written in FX-26's calls answered in a namespace.
    static CALLED: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// How many of the expander written in FX-26's transformers' calls this
/// thread answered in a phase-1 namespace (`call_procedural`): for tests.
pub fn called_for_fx26() -> u64 {
    CALLED.with(|c| c.get())
}

/// How many namespaces this thread has made: for tests, that each
/// expansion has its own.
pub fn made() -> u64 {
    MADE.with(|m| m.get())
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
        let n = MADE.with(|m| m.get());
        Phase1::made_at(rt, format!("%phase1:{n}"))
    }

    /// The runtime's current namespace, an expansion's: made if it has none.
    pub fn current(rt: &mut Runtime) -> Result<Phase1, String> {
        Phase1::current_for(rt, &[])
    }

    /// The expansion's namespace of the phase-1 forms `forms`
    /// (`begin-for-syntax`'s, in order), made if it has none: the standard
    /// environment, the prelude, then `forms`, defined there. A transformer
    /// runs in the namespace of the forms in force where it was defined, so
    /// that what it names is what was there, whatever was defined after or
    /// in another file (`docs/research/typed-macros.md`, "for-syntax").
    pub fn current_for(rt: &mut Runtime, forms: &[String]) -> Result<Phase1, String> {
        let global = if forms.is_empty() { CURRENT.to_string() } else { format!("{CURRENT}:{:016x}", forms_digest(forms)) };
        if crate::stage::global(rt, &global).is_some_and(|v| v != Value::FALSE) {
            return Ok(Phase1 { global });
        }
        let p = Phase1::made_at(rt, global.clone())?;
        // Each made one's global listed, for the expansion's end.
        let name = rt.heap.make_string(&global);
        let base = rt.heap.push_root(name);
        let all = crate::stage::global(rt, ALL).unwrap_or(Value::NULL);
        let l = rt.heap.cons(rt.heap.root_at(base), all);
        rt.heap.pop_roots_to(base);
        let sym = rt.heap.intern(ALL);
        let slot = rt.heap.symbol_ref(sym);
        rt.heap.set_global_at(&slot, l);
        if let Err(e) = p.define_forms(rt, forms) {
            let sym = rt.heap.intern(&global);
            let slot = rt.heap.symbol_ref(sym);
            rt.heap.set_global_at(&slot, Value::FALSE);
            return Err(e);
        }
        Ok(p)
    }

    /// A namespace of its own made in `rt` ([`Phase1::new`]), `forms`
    /// defined in it: the transformers' session's, for those forms.
    pub fn with_forms(rt: &mut Runtime, forms: &[String]) -> Result<Phase1, String> {
        let p = Phase1::new(rt)?;
        p.define_forms(rt, forms)?;
        Ok(p)
    }

    /// Phase-1 forms `forms` checked, compiled and run in the namespace,
    /// in order; or why one was refused.
    fn define_forms(&self, rt: &mut Runtime, forms: &[String]) -> Result<(), String> {
        for f in forms {
            self.run(rt, &format!("{f}\n"), MORE)?;
        }
        Ok(())
    }

    /// The runtime's current namespaces ended, if it has any: an
    /// expansion's end (`Fx26Session::expansion`).
    pub fn end_current(rt: &mut Runtime) {
        let mut l = crate::stage::global(rt, ALL).unwrap_or(Value::NULL);
        let mut globals = vec![CURRENT.to_string()];
        while l.is_pair() {
            globals.push(rt.heap.string_to_rust(rt.heap.car(l)));
            l = rt.heap.cdr(l);
        }
        for g in globals {
            if crate::stage::global(rt, &g).is_some_and(|v| v != Value::FALSE) {
                Phase1 { global: g }.end(rt);
            }
        }
        let sym = rt.heap.intern(ALL);
        let slot = rt.heap.symbol_ref(sym);
        rt.heap.set_global_at(&slot, Value::NULL);
    }

    /// The transformer of `key` (its style and text) defined in the
    /// namespace, its global, if it is; and how many are.
    fn defined_of(&self, rt: &mut Runtime, key: &str) -> (Option<String>, usize) {
        let defined = format!("{}:defined", self.global);
        // `((key . name) …)`, the newest first.
        let mut l = crate::stage::global(rt, &defined).unwrap_or(Value::NULL);
        let mut n = 0;
        while l.is_pair() {
            let entry = rt.heap.car(l);
            if rt.heap.string_to_rust(rt.heap.car(entry)) == key {
                return (Some(rt.heap.symbol_name(rt.heap.cdr(entry))), n);
            }
            n += 1;
            l = rt.heap.cdr(l);
        }
        (None, n)
    }

    /// Transformer `code`, of style `ty` (`key` its style and text), defined
    /// in the namespace if it is not yet, `procedural::helpers` around it: the
    /// global it is; or why it was not defined.
    pub fn transformer(&self, rt: &mut Runtime, ty: &str, key: &str, code: &str) -> Result<String, String> {
        let defined = format!("{}:defined", self.global);
        let (n, count) = self.defined_of(rt, key);
        if let Some(n) = n {
            return Ok(n);
        }
        let name = format!("%transformer:{count}");
        self.define(rt, &name, ty, code)?;
        let k = rt.heap.make_string(key);
        let base = rt.heap.push_root(k);
        let sym = rt.heap.intern(&name);
        let entry = rt.heap.cons(rt.heap.root_at(base), sym);
        rt.heap.push_root(entry);
        let old = crate::stage::global(rt, &defined).unwrap_or(Value::NULL);
        let entry = rt.heap.root_at(base + 1);
        let l = rt.heap.cons(entry, old);
        rt.heap.pop_roots_to(base);
        let dsym = rt.heap.intern(&defined);
        let slot = rt.heap.symbol_ref(dsym);
        rt.heap.set_global_at(&slot, l);
        Ok(name)
    }

    /// A namespace made at global `global`.
    fn made_at(rt: &mut Runtime, global: String) -> Result<Phase1, String> {
        let make = crate::stage::global(rt, MAKE).ok_or("phase 1 needs the front end compiled")?;
        let fe = fixpt_runtime::prim::call_front_end(rt, make, &[])?;
        MADE.with(|m| m.set(m.get() + 1));
        let p = Phase1 { global };
        let sym = rt.heap.intern(&p.global);
        let slot = rt.heap.symbol_ref(sym);
        rt.heap.set_global_at(&slot, fe);
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
        // Its failure said as the transformer's own, as the transformers'
        // session says it, not as the machine's.
        on_cellular(rt, |rt| fixpt_runtime::prim::enter_word(rt, f, &args))
            .map_err(|e| e.strip_prefix("cellular word: ").map_or(e.clone(), str::to_string))
    }

    /// The namespace let go: its front end, and what it defined, garbage.
    pub fn end(self, rt: &mut Runtime) {
        for g in [self.global.clone(), format!("{}:defined", self.global)] {
            let sym = rt.heap.intern(&g);
            let slot = rt.heap.symbol_ref(sym);
            rt.heap.set_global_at(&slot, Value::FALSE);
        }
    }

    fn front_end(&self, rt: &mut Runtime) -> Value {
        let sym = rt.heap.intern(&self.global);
        rt.heap.global_of(sym)
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

/// Transformer `code`, of `style`, called on `datum` in expansion `made`, in
/// `rt`'s current namespace ([`Phase1::current`]), the namespace made and
/// the transformer defined there if they are not yet: what it gave, raw
/// (its caller makes it syntax before anything collects); or why it failed.
/// None where `rt` has no phase 1 (its front end not compiled), where the
/// transformers' session runs it. Both front ends' expanders call it, so
/// both run the one closure.
///
/// Either expander may define, inside its own parse: a definition is a
/// parse of the namespace's own front end, whose reader, parser and
/// expander, with their state, are its own (the conductor makes them for
/// each front end), so the parse it is inside is left as it was.
pub(crate) fn run_transformer(rt: &mut Runtime, style: crate::macros::procedural::Style, code: &str, forms: &[String], datum: Value) -> Option<Result<Value, String>> {
    use crate::macros::procedural;
    let base = rt.heap.push_root(datum);
    let out = (|| {
        let key = procedural::key(style, code);
        // No phase 1 here at all (its front end not compiled, or the
        // standard environment not read): apart. A phase-1 form refused:
        // the transformer's failure.
        let plain = Phase1::current(rt).ok()?;
        let ph = if forms.is_empty() {
            plain
        } else {
            match Phase1::current_for(rt, forms) {
                Ok(ph) => ph,
                Err(e) => return Some(Err(e)),
            }
        };
        let global = match ph.transformer(rt, style.ty(), &key, &procedural::helpers(code)) {
            Ok(g) => g,
            Err(e) => return Some(Err(e)),
        };
        let d = rt.heap.root_at(base);
        Some(call_transformer(rt, &ph, &global, style, d))
    })();
    rt.heap.pop_roots_to(base);
    out
}

/// Transformer `global` of namespace `ph`, of `style`, called on `datum` in
/// expansion `made`: what it gave, raw; or why it failed. Its second
/// argument and third as its style has them (a renamer of the expansion and
/// a comparer; or the use's or the macro's environment).
pub(crate) fn call_transformer(rt: &mut Runtime, ph: &Phase1, global: &str, style: crate::macros::procedural::Style, datum: Value) -> Result<Value, String> {
    use crate::macros::procedural::{self, Style};
    let base = rt.heap.push_root(datum);
    let out = (|| {
        let second = match style {
            Style::Er => ph.value(rt, "%er-rename").ok_or("no `%er-rename` in phase 1")?,
            Style::Sc => rt.heap.intern(procedural::USE_ENV),
            Style::Rsc => rt.heap.intern(procedural::MACRO_ENV),
        };
        rt.heap.push_root(second);
        if let Style::Er = style {
            let compare = ph.value(rt, "%er-compare").unwrap_or(Value::FALSE);
            rt.heap.push_root(compare);
        }
        // Where a transformer's call collects (`TODO.md` §278): a test's, on
        // either side of it, what it is given and gives rooted; the Rust
        // expander's syntax tenured, moved by neither.
        crate::heap_syn::collect_young_if_asked_in(&mut rt.heap);
        let args: Vec<Value> = (base..rt.heap.root_count()).map(|i| rt.heap.root_at(i)).collect();
        let out = ph.call(rt, global, &args)?;
        let at = rt.heap.push_root(out);
        crate::heap_syn::collect_young_if_asked_in(&mut rt.heap);
        Ok(rt.heap.root_at(at))
    })();
    rt.heap.pop_roots_to(base);
    out
}

/// What `%fx26-call-procedural` does (`Runtime::procedural`), for the
/// expander written in FX-26: its arguments a style (0 explicit renaming, 1
/// syntactic closures, 2 reversed), the transformer's text, the use's
/// datum, the expansion's tag (`K.N`, which no transformer is given now:
/// the expander makes `rename`'s aliases its own, `procedural::tagged`),
/// and the phase-1 forms in force where it was
/// defined (a list of texts, `begin-for-syntax`'s); `(sum ok datum)`, what the transformer gave, or
/// `(sum failed why)`. In the expansion's namespace, made and the
/// transformer defined there if they are not yet; else, where the runtime
/// has no phase 1, in the transformers' session, the datum and what it gave
/// copied between the heaps (`procedural::apply_copied`).
pub fn call_procedural(rt: &mut Runtime, a: &[Value]) -> Result<Value, String> {
    use crate::macros::procedural::Style;
    let style = match a[0].as_fixnum() {
        0 => Style::Er,
        1 => Style::Sc,
        _ => Style::Rsc,
    };
    let code = rt.heap.string_to_rust(a[1]);
    // The phase-1 forms in force where it was defined, a list of texts.
    let mut forms = Vec::new();
    let mut l = a[4];
    while l.is_pair() {
        forms.push(rt.heap.string_to_rust(rt.heap.car(l)));
        l = rt.heap.cdr(l);
    }
    let out = match run_transformer(rt, style, &code, &forms, a[2]) {
        Some(out) => {
            CALLED.with(|c| c.set(c.get() + 1));
            out
        }
        None => crate::macros::procedural::apply_copied(style, &code, &forms, &mut rt.heap, a[2]),
    };
    Ok(match out {
        Ok(v) => crate::sessions::sum(rt, "ok", v),
        Err(why) => {
            let why = rt.heap.make_string(&why);
            crate::sessions::sum(rt, "failed", why)
        }
    })
}
