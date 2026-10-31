//! Sessions on the checker written in FX-26 (`TODO.md` §189, step 2): on
//! the machines of the compilers written in FX-26, a session's checker is
//! the one of a front end of the session's own (the conductor's
//! `make-session-compiler`, kept in the session's third field), whose
//! checker holds the session's definitions as the REPL's holds a
//! program's (`check-more`), and whose compiler, whose globals are the
//! session's, compiles from what that checker found. So a session is all
//! in the heap: its front end, and its generation, kept in its second field
//! (`sessions.rs`'s `S_INDEX`, -2 less it, so that it is told apart from a
//! Rust checker's state's index).
//!
//! Each step is the conductor's `session-step`, given the code wrapped as
//! `sessions.rs` wraps it: checked first (the session's first, its module
//! and its values' definitions), kept and compiled (an expression; a
//! commit, into the procedure `go` calls), or tried and not kept (a
//! pending definition, its type found).

use crate::sessions::{expression, failed, is_definition, is_pending, sum, text};
use crate::stage::{staged_parts, Parts, Wrapped};
use fixpt_heap::Value;
use fixpt_runtime::Runtime;

const PRODUCT: u8 = fixpt_heap::layout::kind("product");
const S_MODULE: usize = 0;
const S_INDEX: usize = 1;
const S_COMPILER: usize = 2;

/// The conductor's entry that makes a session's front end, and the fields
/// of what it makes, from 1: a global made, a step, whether re-runs wait,
/// whether reading a global is an effect, a global's type and users.
const MAKE_COMPILER: &str = "fx26-native:make-session-compiler";
const E_GLOBAL: usize = 2;
const E_STEP: usize = 4;
const E_DEFER: usize = 5;
const E_GLOBALS_EFFECTS: usize = 6;
const E_REDEFINES: usize = 7;

/// How `session-step` checks: the first step, checked alone; more, kept;
/// tried, not kept.
const FIRST: i64 = 0;
const MORE: i64 = 1;
const TRY: i64 = 2;

/// Whether the session `s` is on this checker, or new where this
/// checker can be its (a front end that is compiled, and a module's type
/// that names no region of its own: those this checker cannot bind for a
/// session's top level yet).
pub(crate) fn takes(rt: &mut Runtime, s: Value, parts: Option<&Parts>) -> bool {
    match rt.heap.obj_ref(s, S_INDEX).as_fixnum() {
        i if i <= -2 => true,
        -1 => crate::stage::global(rt, MAKE_COMPILER).is_some() && parts.is_none_or(|p| p.regions.is_empty()),
        _ => false,
    }
}

/// The session at `base`'s generation: how many commits it has had.
fn generation(rt: &Runtime, base: usize) -> i64 {
    -2 - rt.heap.obj_ref(rt.heap.root_at(base), S_INDEX).as_fixnum()
}

fn set_generation(rt: &mut Runtime, base: usize, g: i64) {
    let s = rt.heap.root_at(base);
    rt.heap.obj_set(s, S_INDEX, Value::fixnum(-2 - g));
}

/// The session at `base`'s front end, made at its first use: given the
/// module, `stage-module` a global of the module itself; reading its
/// globals not an effect of a step's code (each step's type says it reads
/// the session); re-runs waiting; then `M`'s values each a global of its
/// name, which the session's own may shadow.
fn front_end(rt: &mut Runtime, base: usize, parts: &Parts) -> Result<Result<Value, Value>, String> {
    let s = rt.heap.root_at(base);
    let made = rt.heap.obj_ref(s, S_COMPILER);
    if rt.heap.obj_ref(s, S_INDEX).as_fixnum() <= -2 && made != Value::FALSE {
        return Ok(Ok(made));
    }
    let make = crate::stage::global(rt, MAKE_COMPILER).ok_or("this machine cannot keep sessions: its front end is not compiled")?;
    let fe = fixpt_runtime::prim::call_front_end(rt, make, &[])?;
    let s = rt.heap.root_at(base);
    rt.heap.obj_set(s, S_COMPILER, fe);
    call(rt, base, E_GLOBALS_EFFECTS, &[Value::FALSE])?;
    call(rt, base, E_DEFER, &[Value::TRUE])?;
    let name = rt.heap.intern("stage-module");
    let cell = call(rt, base, E_GLOBAL, &[name])?;
    let m = rt.heap.obj_ref(rt.heap.root_at(base), S_MODULE);
    rt.heap.set_bloblet_slot(cell, fixpt_heap::layout::cellular::GLOBAL_VALUE, m);
    let mt = &parts.mt;
    let seed = format!("(define stage-module (the {mt} %fasl-value))\n");
    if let Err(refused) = step(rt, base, &Wrapped::of(String::new(), &seed, "", &seed, 0), FIRST, "", false)? {
        return Ok(Err(refused));
    }
    let values: String = module_values(mt).iter().map(|n| format!("(define {n} (with stage-module {n}))\n")).collect();
    if !values.is_empty() {
        match step(rt, base, &Wrapped::of(String::new(), &values, "", &values, 0), MORE, "", false)? {
            Ok(word) => {
                let run = rt.run_word.ok_or("no cellular machine is installed")?;
                run(rt, word, &[])?;
            }
            Err(refused) => return Ok(Err(refused)),
        }
    }
    set_generation(rt, base, 0);
    Ok(Ok(rt.heap.obj_ref(rt.heap.root_at(base), S_COMPILER)))
}

/// The names of the values of module type `mt`, printed whole: each `(val
/// name T)` of it, as written there.
fn module_values(mt: &str) -> Vec<String> {
    let mut interner = fixpt_read::Interner::new();
    let Ok(forms) = fixpt_read::Reader::new(mt, fixpt_read::FileId(0), fixpt_read::SyntaxProfile::FX91, &mut interner).read_all() else { return Vec::new() };
    let Some(items) = forms.first().and_then(|f| f.as_proper_list()) else { return Vec::new() };
    items
        .iter()
        .filter_map(|i| match i.as_proper_list() {
            Some([head, name, _]) if head.as_symbol().is_some_and(|h| interner.name(h) == "val") => name.as_symbol().map(|n| fixpt_read::escape_symbol(interner.name(n))),
            _ => None,
        })
        .collect()
}

/// Entry `i` of the session at `base`'s front end, called with `args`.
fn call(rt: &mut Runtime, base: usize, i: usize, args: &[Value]) -> Result<Value, String> {
    let fe = rt.heap.obj_ref(rt.heap.root_at(base), S_COMPILER);
    let f = rt.heap.bloblet_slot(fe, i + 1);
    let fuel = std::mem::replace(&mut rt.word_fuel, u64::MAX);
    let out = fixpt_runtime::prim::call_front_end(rt, f, args);
    rt.word_fuel = fuel;
    out
}

/// `w` given the session at `base`'s `session-step`, checked as `how`
/// says, `name` the global a trial's type is of, compiled into the
/// procedure that runs it if `deferred`: the word (or that procedure's
/// word), or, tried, the type; or the refusal, `(sum failed why)`.
fn step(rt: &mut Runtime, base: usize, w: &Wrapped, how: i64, name: &str, deferred: bool) -> Result<Result<Value, Value>, String> {
    let (native, registers) = crate::stage::flags(rt).ok_or("this machine cannot keep sessions")?;
    let standard = crate::stage::standard(rt).ok_or("this machine cannot keep sessions")?;
    let mark = rt.heap.push_root(standard);
    let whole = rt.heap.make_string(&w.whole);
    rt.heap.push_root(whole);
    let name = rt.heap.intern(if name.is_empty() { "%none" } else { name });
    let [standard, whole] = [0, 1].map(|i| rt.heap.root_at(mark + i));
    rt.heap.pop_roots_to(mark);
    let made = how != TRY;
    let args = [standard, whole, Value::fixnum(w.skip), Value::fixnum(w.len), Value::fixnum(how), name, Value::boolean(made), Value::boolean(deferred), Value::boolean(native), Value::boolean(registers)];
    let out = call(rt, base, E_STEP, &args)?;
    let tag = rt.heap.symbol_name(rt.heap.bloblet_slot(out, 2));
    let payload = rt.heap.bloblet_slot(out, 3);
    Ok(match tag.as_str() {
        "made" | "typed" | "checked" => Ok(payload),
        _ => Err(out),
    })
}

/// What `%fx26-session-check` does on this checker: an expression, the
/// procedure that evaluates it, `(sum ok (sum expression p))`; a
/// definition, pending, `(sum ok (sum definition d))`; or the refusal.
pub(crate) fn check(rt: &mut Runtime, base: usize, staged: Value, given: Value) -> Result<Value, String> {
    let (parts, code) = staged_parts(rt, staged, given).ok_or("this machine cannot stage code")?;
    if !parts.regions.is_empty() {
        return Ok(failed(rt, "refused", "a session's code is not checked against a region of its own on this machine yet"));
    }
    let code_text = fixpt_runtime::print::write_value(&rt.heap, code);
    // Rooted while the session's front end is made, which collects.
    let mark = rt.heap.push_root(code);
    let made = front_end(rt, base, &parts);
    let code = rt.heap.root_at(mark);
    rt.heap.pop_roots_to(mark);
    if let Err(refused) = made? {
        return Ok(refused);
    }
    if is_definition(rt, code) {
        return check_define(rt, base, &parts, code, &code_text);
    }
    let w = expression(&parts.e, &parts.r, &code_text);
    match step(rt, base, &w, MORE, "", false)? {
        Ok(word) => {
            let run = rt.run_word.ok_or("no cellular machine is installed")?;
            let p = run(rt, word, &[])?;
            let p = sum(rt, "expression", p);
            Ok(sum(rt, "ok", p))
        }
        Err(refused) => Ok(refused),
    }
}

/// A definition checked against the session at `base`: `code`, `(define
/// name init)` or `(define name type init)`; its type found if not
/// written, and its initializer, unless a `lambda`, tried within `E`; the
/// form, its type written, tried too; the pending definition. Nothing kept.
fn check_define(rt: &mut Runtime, base: usize, against: &Parts, code: Value, text: &str) -> Result<Value, String> {
    let len = text.chars().count() as i64;
    let usage = "a definition is `(define name init)` or `(define name type init)`";
    let parts = rt.heap.list_to_vec(code).unwrap_or_default();
    let is = |v: Value, n: &str| rt.heap.is_a(v, fixpt_heap::ObjType::Symbol) && rt.heap.symbol_name(v) == n;
    let symbol = |v: Value| rt.heap.is_a(v, fixpt_heap::ObjType::Symbol);
    let (name, ty, init) = match parts[..] {
        [d, n, init] if is(d, "define") && symbol(n) => (n, None, init),
        [d, n, t, init] if is(d, "define") && symbol(n) => (n, Some(t), init),
        _ => return Ok(fixpt_runtime::prim::stage_failed(rt, "malformed", usage, 0, len)),
    };
    let write = |rt: &Runtime, v: Value| fixpt_runtime::print::write_value(&rt.heap, v);
    let name = rt.heap.symbol_name(name);
    let shown = fixpt_read::escape_symbol(&name);
    let init_text = write(rt, init);
    let lambda = rt.heap.list_to_vec(init).and_then(|l| l.first().copied()).is_some_and(|h| is(h, "lambda"));
    let ty = match ty.map(|t| write(rt, t)) {
        Some(t) => t,
        None => match step(rt, base, &Wrapped::of(String::new(), text, "\n", text, 0), TRY, &name, false)? {
            Ok(t) if rt.heap.string_to_rust(t).is_empty() => return Ok(fixpt_runtime::prim::stage_failed(rt, "malformed", usage, 0, len)),
            Ok(t) => rt.heap.string_to_rust(t),
            Err(refused) => return Ok(refused),
        },
    };
    let e = &against.e;
    let at = text.find(&init_text).map_or(0, |i| text[..i].chars().count());
    let bounded = Wrapped::of(format!("(the (subr {e} () {ty})\n(lambda ()\n"), &init_text, "\n))\n", text, at);
    if !lambda && let Err(refused) = step(rt, base, &bounded, TRY, "", false)? {
        return Ok(refused);
    }
    let form = format!("(define {shown} {ty} {init_text})");
    if let Err(refused) = step(rt, base, &Wrapped::of(String::new(), &form, "\n", &form, 0), TRY, &name, false)? {
        return Ok(refused);
    }
    let generation = generation(rt, base);
    let d = crate::sessions::pending(rt, base, generation, &name, &ty, &form);
    let d = sum(rt, "definition", d);
    Ok(sum(rt, "ok", d))
}

/// `session-redefines` on this checker: `(sum fresh #u)`, or `(sum
/// redefines r)`, `r` the name, its type and the new one, and the
/// session's definitions that use it.
pub(crate) fn redefines(rt: &mut Runtime, base: usize, d: Value) -> Result<Value, String> {
    if !is_pending(rt, d) || rt.heap.obj_ref(rt.heap.root_at(base), S_COMPILER) == Value::FALSE {
        return Ok(sum(rt, "fresh", Value::UNIT));
    }
    let mark = rt.heap.push_root(d);
    let name = rt.heap.intern(&text(rt, rt.heap.obj_ref(d, crate::sessions::P_NAME)));
    let found = call(rt, base, E_REDEFINES, &[name])?;
    let d = rt.heap.root_at(mark);
    if !found.is_pair() {
        rt.heap.pop_roots_to(mark);
        return Ok(sum(rt, "fresh", Value::UNIT));
    }
    let found = rt.heap.car(found);
    rt.heap.push_root(found);
    let (old, users) = (rt.heap.bloblet_slot(found, 2), rt.heap.bloblet_slot(found, 3));
    let [name, new] = [crate::sessions::P_NAME, crate::sessions::P_TYPE].map(|i| rt.heap.obj_ref(d, i));
    let r = rt.heap.make_frozen(PRODUCT, &[name, old, new, users]);
    rt.heap.pop_roots_to(mark);
    Ok(sum(rt, "redefines", r))
}

/// `%session-ready` on this checker: `d` committed as `decision` says,
/// unless stale or refused: the form kept by the session's checker, re-runs
/// waiting (`shadow`) or not (`rerun`), and it and what runs again compiled
/// into the procedure that runs them, `(sum go p)`, for the program to
/// call; or the refusal.
pub(crate) fn ready(rt: &mut Runtime, base: usize, d: Value, decision: Value) -> Result<Value, String> {
    let s = rt.heap.root_at(base);
    if !is_pending(rt, d) || rt.heap.obj_ref(d, crate::sessions::P_SESSION) != s {
        return Ok(failed(rt, "stale", "this definition was checked against another session"));
    }
    if rt.heap.obj_ref(d, crate::sessions::P_USED) != Value::FALSE {
        return Ok(failed(rt, "stale", "this definition was committed already"));
    }
    if rt.heap.obj_ref(d, crate::sessions::P_GENERATION).as_fixnum() != generation(rt, base) {
        return Ok(failed(rt, "stale", "the session changed since this definition was checked: check it again"));
    }
    let decision = crate::sessions::decided(rt, decision);
    let mark = rt.heap.push_root(d);
    let name = text(rt, rt.heap.obj_ref(d, crate::sessions::P_NAME));
    let form = text(rt, rt.heap.obj_ref(d, crate::sessions::P_FORM));
    let sym = rt.heap.intern(&name);
    let exists = call(rt, base, E_REDEFINES, &[sym])?.is_pair();
    if exists && decision == "refuse" {
        rt.heap.pop_roots_to(mark);
        return Ok(failed(rt, "refused", &format!("`{name}` is defined already, and the redefinition was refused")));
    }
    let rerun = exists && decision == "rerun";
    if rerun {
        call(rt, base, E_DEFER, &[Value::FALSE])?;
    }
    let made = step(rt, base, &Wrapped::of(String::new(), &form, "\n", &form, 0), MORE, "", true);
    if rerun {
        call(rt, base, E_DEFER, &[Value::TRUE])?;
    }
    let d = rt.heap.root_at(mark);
    rt.heap.pop_roots_to(mark);
    match made? {
        Ok(word) => {
            rt.heap.obj_set(d, crate::sessions::P_USED, Value::TRUE);
            let g = generation(rt, base);
            set_generation(rt, base, g + 1);
            let run = rt.run_word.ok_or("no cellular machine is installed")?;
            let p = run(rt, word, &[])?;
            Ok(sum(rt, "go", p))
        }
        Err(refused) => Ok(refused),
    }
}
