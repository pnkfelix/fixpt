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

use crate::sessions::{failed, is_definition, is_pending, strings, sum, text};
use crate::stage::{staged_parts, Wrapped};
use fixpt_heap::Value;
use fixpt_runtime::Runtime;

const PRODUCT: u8 = fixpt_heap::layout::kind("product");
const S_MODULE: usize = 0;
const S_INDEX: usize = 1;
const S_COMPILER: usize = 2;
/// On the evaluator, what is run of the session as text: a pair of the
/// texts that define `m`'s values, not yet run, and each definition
/// committed, by name, its form's text, newest first.
const S_TEXTS: usize = 3;

/// The conductor's entry that makes a session's front end, and the fields
/// of what it makes, from 1: a global made, a step, whether re-runs wait,
/// whether reading a global is an effect, a global's type and users.
const MAKE_COMPILER: &str = "fx26-native:make-session-compiler";
const E_GLOBAL: usize = 2;
const E_STEP: usize = 4;
const E_DEFER: usize = 5;
const E_GLOBALS_EFFECTS: usize = 6;
const E_REDEFINES: usize = 7;
const E_RUNS: usize = 8;

/// How `session-step` checks: the first step, checked alone; more, kept;
/// tried, not kept.
const FIRST: i64 = 0;
const MORE: i64 = 1;
const TRY: i64 = 2;

thread_local! {
    /// The names a session's check's steps give its types, each a rep in its
    /// binary form (`stage::step_reps`), and its module's values' names; for
    /// the check, none outside it (`StepNamed`).
    static STEP_NAMED: std::cell::RefCell<Vec<(String, Vec<u8>)>> = const { std::cell::RefCell::new(Vec::new()) };
    static STEP_VALUES: std::cell::RefCell<Option<Vec<String>>> = const { std::cell::RefCell::new(None) };
}

/// The step names set for a check, unset as it ends.
struct StepNamed;

impl StepNamed {
    fn set(reps: Option<crate::stage::StepReps>) -> StepNamed {
        let (named, values) = match reps {
            Some(r) => (r.named, Some(r.values)),
            None => (Vec::new(), None),
        };
        STEP_NAMED.with(|n| *n.borrow_mut() = named);
        STEP_VALUES.with(|v| *v.borrow_mut() = values);
        StepNamed
    }
}

impl Drop for StepNamed {
    fn drop(&mut self) {
        STEP_NAMED.with(|n| n.borrow_mut().clear());
        STEP_VALUES.with(|v| *v.borrow_mut() = None);
    }
}

/// `named` as `session-step` takes it: a list of products of a symbol and a
/// bytevector.
fn named_list(rt: &mut Runtime, named: &[(String, Vec<u8>)]) -> Value {
    let mut l = Value::NULL;
    for (n, bytes) in named.iter().rev() {
        let base = rt.heap.push_root(l);
        let sym = rt.heap.intern(n);
        rt.heap.push_root(sym);
        let b = rt.heap.make_bytevector(bytes);
        rt.heap.push_root(b);
        let (sym, b) = (rt.heap.root_at(base + 1), rt.heap.root_at(base + 2));
        let p = rt.heap.make_frozen(PRODUCT, &[sym, b]);
        rt.heap.push_root(p);
        let (l0, p) = (rt.heap.root_at(base), rt.heap.root_at(base + 3));
        l = rt.heap.cons(p, l0);
        rt.heap.pop_roots_to(base);
    }
    l
}

/// An expression step's code wrapped, its type named (`%stage-result-type`,
/// `(subr E () R)`).
fn step_expression(code: &str) -> Wrapped {
    let r = crate::stage::RESULT_TYPE;
    Wrapped::of(format!("(the {r}\n(lambda ()\n"), code, "\n))\n", code, 0)
}

/// Whether the session `s` is on this checker, or new where this
/// checker can be its (a front end that is compiled).
pub(crate) fn takes(rt: &mut Runtime, s: Value) -> bool {
    match rt.heap.obj_ref(s, S_INDEX).as_fixnum() {
        i if i <= -2 => true,
        -1 => crate::stage::global(rt, MAKE_COMPILER).is_some(),
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
///
/// On the evaluator (`evaluated`), nothing is compiled: the texts of `m`'s
/// values' definitions are kept, for the evaluator to run before the next
/// step's (`S_TEXTS`).
fn front_end(rt: &mut Runtime, base: usize, evaluated: bool) -> Result<Result<Value, Value>, String> {
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
    // The module's type named, not written (`StepNamed`).
    let mt = crate::stage::MODULE_TYPE;
    let seed = format!("(define stage-module (the {mt} %fasl-value))\n");
    if let Err(refused) = step(rt, base, &Wrapped::of(String::new(), &seed, "", &seed, 0), FIRST, "", false)? {
        return Ok(Err(refused));
    }
    let names = STEP_VALUES.with(|v| v.borrow().clone()).unwrap_or_default();
    let defines: Vec<String> = names.iter().map(|n| format!("(define {n} (with stage-module {n}))\n")).collect();
    let values: String = defines.concat();
    if !values.is_empty() {
        let w = Wrapped::of(String::new(), &values, "", &values, 0);
        let made = if evaluated { step_checked(rt, base, &w)? } else { step(rt, base, &w, MORE, "", false)? };
        match made {
            Ok(word) if !evaluated => {
                let run = rt.run_word.ok_or("no cellular machine is installed")?;
                run(rt, word, &[])?;
            }
            Ok(_) => {}
            Err(refused) => return Ok(Err(refused)),
        }
    }
    if evaluated {
        let seeds = crate::sessions::strings(rt, defines.iter().map(|t| (t.as_str(), None)));
        let texts = rt.heap.cons(seeds, Value::NULL);
        let s = rt.heap.root_at(base);
        rt.heap.obj_set(s, S_TEXTS, texts);
    }
    set_generation(rt, base, 0);
    Ok(Ok(rt.heap.obj_ref(rt.heap.root_at(base), S_COMPILER)))
}

/// Entry `i` of the session at `base`'s front end, called with `args`.
fn call(rt: &mut Runtime, base: usize, i: usize, args: &[Value]) -> Result<Value, String> {
    let fe = rt.heap.obj_ref(rt.heap.root_at(base), S_COMPILER);
    let f = rt.heap.product_field(fe, i);
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
    step_making(rt, base, w, how, name, deferred, how != TRY, &[])
}

/// The same, the type of `rep` (a rep's binary form) the name `w` gives
/// `%stage-type` (`check-more-with`), not read again from text
/// (`docs/research/heap-types.md`, step 4).
fn step_by_rep(rt: &mut Runtime, base: usize, w: &Wrapped, how: i64, name: &str, deferred: bool, rep: &[u8]) -> Result<Result<Value, Value>, String> {
    step_making(rt, base, w, how, name, deferred, how != TRY, rep)
}

/// `w` checked and kept, not compiled (a session on the evaluator):
/// `(sum checked #u)`'s payload; or the refusal.
fn step_checked(rt: &mut Runtime, base: usize, w: &Wrapped) -> Result<Result<Value, Value>, String> {
    step_making(rt, base, w, MORE, "", false, false, &[])
}

#[allow(clippy::too_many_arguments)]
fn step_making(rt: &mut Runtime, base: usize, w: &Wrapped, how: i64, name: &str, deferred: bool, made: bool, rep: &[u8]) -> Result<Result<Value, Value>, String> {
    let (native, registers) = crate::stage::flags(rt).ok_or("this machine cannot keep sessions")?;
    let standard = crate::stage::standard(rt).ok_or("this machine cannot keep sessions")?;
    let mark = rt.heap.push_root(standard);
    let whole = rt.heap.make_string(&w.whole);
    rt.heap.push_root(whole);
    let name = rt.heap.intern(if name.is_empty() { "%none" } else { name });
    rt.heap.push_root(name);
    let rep = rt.heap.make_bytevector(rep);
    rt.heap.push_root(rep);
    // Only the names this step's text gives its types, each imported for it.
    let named: Vec<(String, Vec<u8>)> = STEP_NAMED.with(|n| n.borrow().iter().filter(|(name, _)| w.whole.contains(name.as_str())).cloned().collect());
    let named = named_list(rt, &named);
    let [standard, whole, name, rep] = [0, 1, 2, 3].map(|i| rt.heap.root_at(mark + i));
    rt.heap.pop_roots_to(mark);
    let args = [standard, whole, Value::fixnum(w.skip), Value::fixnum(w.len), Value::fixnum(how), name, Value::boolean(made), Value::boolean(deferred), Value::boolean(native), Value::boolean(registers), rep, named];
    let out = call(rt, base, E_STEP, &args)?;
    let tag = rt.heap.symbol_name(rt.heap.sum_tag(out));
    let payload = rt.heap.sum_payload(out);
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
    // Its types by rep, for each of its steps (`docs/research/heap-types.md`,
    // step 6).
    let Some(reps) = parts.rep.as_deref().and_then(crate::stage::step_reps) else { return Ok(crate::stage::no_rep(rt)) };
    let _named = StepNamed::set(Some(reps));
    let code_text = fixpt_runtime::print::write_value(&rt.heap, code);
    // Rooted while the session's front end is made, which collects.
    let mark = rt.heap.push_root(code);
    let made = front_end(rt, base, false);
    let code = rt.heap.root_at(mark);
    rt.heap.pop_roots_to(mark);
    if let Err(refused) = made? {
        return Ok(refused);
    }
    if is_definition(rt, code) {
        return check_define(rt, base, code, &code_text);
    }
    let w = step_expression(&code_text);
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
fn check_define(rt: &mut Runtime, base: usize, code: Value, text: &str) -> Result<Value, String> {
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
    // The type, written, or found by a trial: its text, and its rep where
    // the trial made one, which the steps after name, not read again.
    let (ty, rep) = match ty.map(|t| write(rt, t)) {
        Some(t) => (t, Vec::new()),
        None => match step(rt, base, &Wrapped::of(String::new(), text, "\n", text, 0), TRY, &name, false)? {
            Ok(found) => {
                let t = rt.heap.string_to_rust(rt.heap.product_field(found, 1));
                if t.is_empty() {
                    return Ok(fixpt_runtime::prim::stage_failed(rt, "malformed", usage, 0, len));
                }
                let r = rt.heap.product_field(found, 2);
                (t, (0..rt.heap.bytevector_len(r)).map(|i| rt.heap.bytevector_ref(r, i)).collect())
            }
            Err(refused) => return Ok(refused),
        },
    };
    let named = if rep.is_empty() { ty.as_str() } else { "%stage-type" };
    let e = crate::stage::EFFECT;
    let at = text.find(&init_text).map_or(0, |i| text[..i].chars().count());
    let bounded = Wrapped::of(format!("(the (subr {e} () {named})\n(lambda ()\n"), &init_text, "\n))\n", text, at);
    if !lambda && let Err(refused) = step_by_rep(rt, base, &bounded, TRY, "", false, &rep)? {
        return Ok(refused);
    }
    let checked = format!("(define {shown} {named} {init_text})");
    if let Err(refused) = step_by_rep(rt, base, &Wrapped::of(String::new(), &checked, "\n", &checked, 0), TRY, &name, false, &rep)? {
        return Ok(refused);
    }
    let form = format!("(define {shown} {ty} {init_text})");
    let generation = generation(rt, base);
    let by_rep = (!rep.is_empty()).then_some((rep.as_slice(), checked.as_str()));
    let d = crate::sessions::pending(rt, base, generation, &name, &ty, &form, by_rep);
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
    let (old, users) = (rt.heap.product_field(found, 1), rt.heap.product_field(found, 2));
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
///
/// On the evaluator (`evaluated`), nothing is compiled: `(sum run forms)`,
/// each form's text and whether it keeps its globals, what defines `m`'s
/// values first if not yet run, for the evaluator to run in the session.
pub(crate) fn ready(rt: &mut Runtime, base: usize, d: Value, decision: &str, evaluated: bool) -> Result<Value, String> {
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
    let w = Wrapped::of(String::new(), &form, "\n", &form, 0);
    // Compiled, by its type's rep where it has one (the form naming it).
    let rep = rt.heap.obj_ref(rt.heap.root_at(mark), crate::sessions::P_REP);
    let by_rep = (rep != Value::FALSE).then(|| {
        let d = rt.heap.root_at(mark);
        let bytes: Vec<u8> = (0..rt.heap.bytevector_len(rep)).map(|i| rt.heap.bytevector_ref(rep, i)).collect();
        (bytes, text(rt, rt.heap.obj_ref(d, crate::sessions::P_REP_FORM)))
    });
    // What the evaluator runs: the form; by rep, the form without its type,
    // checked already, which the evaluator does not check (nor read again).
    let run_form = match &by_rep {
        Some((_, checked)) => checked.replacen(" %stage-type ", " ", 1),
        None => form.clone(),
    };
    let made = match (evaluated, by_rep) {
        // Checked and kept; the evaluator runs the form's text after.
        (true, Some((bytes, checked))) => step_making(rt, base, &Wrapped::of(String::new(), &checked, "\n", &checked, 0), MORE, "", false, false, &bytes),
        (true, None) => step_checked(rt, base, &w),
        (false, Some((bytes, checked))) => step_by_rep(rt, base, &Wrapped::of(String::new(), &checked, "\n", &checked, 0), MORE, "", true, &bytes),
        (false, None) => step(rt, base, &w, MORE, "", true),
    };
    if rerun {
        call(rt, base, E_DEFER, &[Value::TRUE])?;
    }
    let d = rt.heap.root_at(mark);
    rt.heap.pop_roots_to(mark);
    if evaluated {
        return match made? {
            Ok(_) => {
                rt.heap.obj_set(d, crate::sessions::P_USED, Value::TRUE);
                let g = generation(rt, base);
                set_generation(rt, base, g + 1);
                run_texts(rt, base, &name, &run_form)
            }
            Err(refused) => Ok(refused),
        };
    }
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

/// The seeds not yet run, taken: the texts that define `m`'s values.
fn take_seeds(rt: &mut Runtime, base: usize) -> Vec<String> {
    let texts = rt.heap.obj_ref(rt.heap.root_at(base), S_TEXTS);
    if !texts.is_pair() {
        return Vec::new();
    }
    let seeds: Vec<String> = rt.heap.list_to_vec(rt.heap.car(texts)).unwrap_or_default().iter().map(|v| text(rt, *v)).collect();
    rt.heap.set_car(texts, Value::NULL);
    seeds
}

/// Each definition committed, by name, its form's text.
fn committed_texts(rt: &Runtime, base: usize) -> Vec<(String, String)> {
    let texts = rt.heap.obj_ref(rt.heap.root_at(base), S_TEXTS);
    if !texts.is_pair() {
        return Vec::new();
    }
    let entries = rt.heap.list_to_vec(rt.heap.cdr(texts)).unwrap_or_default();
    entries.iter().filter(|e| e.is_pair()).map(|e| (text(rt, rt.heap.car(*e)), text(rt, rt.heap.cdr(*e)))).collect()
}

/// After a commit of `name`, its form `form`, on the evaluator: `form`
/// recorded as `name`'s; then `(sum run forms)`, what defines `m`'s values
/// if not yet run, and each run the checker says the commit makes (it, and
/// each definition run again), its text, and whether it keeps its globals.
fn run_texts(rt: &mut Runtime, base: usize, name: &str, form: &str) -> Result<Value, String> {
    let runs = call(rt, base, E_RUNS, &[])?;
    let runs: Vec<(String, bool)> = rt.heap.list_to_vec(runs).unwrap_or_default().iter().map(|r| (text(rt, rt.heap.product_field(*r, 1)), rt.heap.product_field(*r, 2) != Value::FALSE)).collect();
    let known = committed_texts(rt, base);
    let mut forms: Vec<(String, bool)> = take_seeds(rt, base).into_iter().map(|t| (t, false)).collect();
    for (n, keeps) in runs {
        let t = if n == name { Some(form.to_string()) } else { known.iter().find(|(k, _)| *k == n).map(|(_, t)| t.clone()) };
        if let Some(t) = t {
            forms.push((t, keeps));
        }
    }
    // `name`'s form recorded, before those of other names.
    let mark = rt.heap.push_root(Value::NULL);
    for t in [name, form] {
        let v = rt.heap.make_string(t);
        rt.heap.push_root(v);
    }
    let (n, f) = (rt.heap.root_at(mark + 1), rt.heap.root_at(mark + 2));
    let entry = rt.heap.cons(n, f);
    rt.heap.set_root_at(mark, entry);
    let texts = rt.heap.obj_ref(rt.heap.root_at(base), S_TEXTS);
    let rest = if texts.is_pair() { rt.heap.cdr(texts) } else { Value::NULL };
    let entry = rt.heap.root_at(mark);
    let rest = rt.heap.cons(entry, rest);
    let texts = rt.heap.obj_ref(rt.heap.root_at(base), S_TEXTS);
    if texts.is_pair() {
        rt.heap.set_cdr(texts, rest);
    } else {
        let t = rt.heap.cons(Value::NULL, rest);
        let s = rt.heap.root_at(base);
        rt.heap.obj_set(s, S_TEXTS, t);
    }
    rt.heap.pop_roots_to(mark);
    let list = strings(rt, forms.iter().map(|(t, k)| (t.as_str(), Some(*k))));
    Ok(sum(rt, "run", list))
}

/// What `%fx26-session-eval-check` does on this checker: the code as
/// text, the names of the variables its type names, that type as a rep and
/// the evidence's reps' binary forms (`a`): an expression,
/// `(sum run texts)`, the forms to run, the last's value the procedure
/// that evaluates it; a definition, pending; or the refusal.
pub(crate) fn eval_check(rt: &mut Runtime, base: usize, a: &[Value]) -> Result<Value, String> {
    let code_text = text(rt, a[0]);
    let given = fixpt_runtime::evidence::Given::of_bytes(rt, a[1], a[3]);
    // By the rep the checker made (`a[2]`), for each step.
    let rep = crate::stage::given_rep(rt, a[2], &given);
    let Some(reps) = rep.as_deref().and_then(crate::stage::step_reps) else { return Ok(crate::stage::no_rep(rt)) };
    let _named = StepNamed::set(Some(reps));
    if let Err(refused) = front_end(rt, base, true)? {
        return Ok(refused);
    }
    let mut interner = std::mem::take(&mut rt.interner);
    let read = fixpt_read::Reader::new(&code_text, fixpt_read::FileId(0), fixpt_read::SyntaxProfile::FX91, &mut interner).read_all();
    rt.interner = interner;
    let code = match read.as_deref() {
        Ok([one]) => fixpt_runtime::port::syntax_to_value(rt, one),
        Ok(_) => return Ok(failed(rt, "unread", "the code is not one whole expression")),
        Err(e) => return Ok(failed(rt, "unread", &e.message)),
    };
    if is_definition(rt, code) {
        return check_define(rt, base, code, &code_text);
    }
    let w = step_expression(&code_text);
    match step_checked(rt, base, &w)? {
        Ok(_) => {
            let mut texts = take_seeds(rt, base);
            texts.push(w.whole.clone());
            let list = strings(rt, texts.iter().map(|t| (t.as_str(), None)));
            Ok(sum(rt, "run", list))
        }
        Err(refused) => Ok(refused),
    }
}
