//! Sessions (`docs/research/eval.md`, "Sessions"): definitions that last
//! between pieces of code a program stages against a module, each made in
//! two steps, checked (a pending definition) and committed, the program
//! deciding between them. What the runtime's `%fx26-session-…` primitives
//! ask of a checker ([`op`], installed by the session).
//!
//! A session's state is a checker written in Rust, of the standard
//! environment and the session's own definitions, as the REPL's is of a
//! program's: so a redefinition is the REPL's (`Checker::top_defining`),
//! re-runs waiting or not as the decision says, and a pending definition is
//! a check that leaves the checker as it was (`try_top`). The session, a
//! vector `#(m index)`, names its state by its index here, made at its
//! first use, when the module's type is known (`seeded`): a global holding
//! `m`, and one for each of `m`'s values, which the session's own may
//! shadow.
//!
//! Lowered (`rs-scheme-vm`): each step's Scheme is given back as a datum,
//! for the runtime to give `eval`, each session's globals named by a prefix
//! of its own. Elsewhere, not yet: a refusal says so.

use crate::check::Checker;
use crate::lower::Globals;
use crate::stage::{staged_parts, sx_value, Wrapped};
use crate::sx::Code;
use crate::top::Top;
use fixpt_heap::Value;
use fixpt_runtime::Runtime;
use std::cell::RefCell;

const SUM: u8 = fixpt_heap::layout::kind("sum");
const PRODUCT: u8 = fixpt_heap::layout::kind("product");

/// A session's state: its checker, the lowering's names of its globals,
/// how many commits it has had, and the Scheme that defines `m`'s values'
/// globals, until the first code given `eval` runs it first.
struct State {
    checker: Checker,
    globals: Globals,
    generation: i64,
    seeds: Code,
}

thread_local! {
    static SESSIONS: RefCell<Vec<State>> = const { RefCell::new(Vec::new()) };
}

/// The session's fields, and a pending definition's: `#(session generation
/// name type form used)`, the form `(define name type init)` as text.
const S_MODULE: usize = 0;
const S_INDEX: usize = 1;
const P_SESSION: usize = 0;
const P_GENERATION: usize = 1;
const P_NAME: usize = 2;
const P_TYPE: usize = 3;
const P_FORM: usize = 4;
const P_USED: usize = 5;

/// Session operation `op` on `a` (the runtime's `sessions`).
pub fn op(rt: &mut Runtime, op: &str, a: &[Value]) -> Result<Value, String> {
    if !is_session(rt, a[0]) {
        return Err("not a session".to_string());
    }
    match op {
        "lower" => lower(rt, a[0], a[1], a[2] != Value::FALSE),
        "redefines" => Ok(redefines(rt, a[0], a[1])),
        "commit-lower" => commit_lower(rt, a[0], a[1], a[2]),
        _ => Err("this machine cannot keep sessions yet".to_string()),
    }
}

fn is_session(rt: &Runtime, s: Value) -> bool {
    rt.heap.is_a(s, fixpt_heap::ObjType::Vector) && rt.heap.obj_len(s) == 2
}

fn sum(rt: &mut Runtime, tag: &str, v: Value) -> Value {
    let tag = rt.heap.intern(tag);
    rt.heap.make_frozen(SUM, &[tag, v])
}

fn failed(rt: &mut Runtime, kind: &str, why: &str) -> Value {
    fixpt_runtime::prim::stage_failed(rt, kind, why, 0, 0)
}

/// `f` of session `s`'s state, made first if `s` has none, of module type
/// `mt` (printed whole): the checker given `m` as `stage-module`, and each
/// of its values as a global of its name, whose Scheme runs before the
/// first code given `eval` (`State::seeds`).
fn seeded<T>(rt: &mut Runtime, s: Value, mt: &str, f: impl FnOnce(&mut Runtime, &mut State) -> T) -> Result<T, String> {
    let index = rt.heap.obj_ref(s, S_INDEX).as_fixnum();
    let mut seeds = Code::default();
    let index = if index >= 0 {
        index as usize
    } else {
        let i = SESSIONS.with(|ss| ss.borrow().len());
        let mut checker = Checker::new();
        checker.defer_reruns = true;
        // Reading a session's global is reading the session, which its
        // forms' types say (`(read r)`), not part of the code's `E`.
        checker.globals_effects = false;
        let mut globals = Globals::with_prefix(&format!("fx26-session-{i}:"));
        let module = checker.interner.intern("stage-module");
        let made = define(&mut checker, &format!("(define stage-module (the {mt} %fasl-value))"))?;
        // The module's own global holds `m` itself, given here, not made.
        let _ = made;
        let global = globals.define(&checker, module);
        let m = rt.heap.obj_ref(s, S_MODULE);
        let sym = rt.heap.intern(&global);
        let slot = rt.heap.symbol_global_slot(sym);
        rt.heap.set_global(slot, m);
        let vals = match checker.global_type(module).map(|t| checker.arena.get(checker.arena.resolve(t)).clone()) {
            Some(crate::ast::Ty::Module { vals, .. }) => vals.iter().map(|(n, _)| checker.interner.name(*n).to_string()).collect::<Vec<_>>(),
            _ => return Err("a session's module is not a module".to_string()),
        };
        for n in vals {
            let n = fixpt_read::escape_symbol(&n);
            let top = define(&mut checker, &format!("(define {n} (with stage-module {n}))"))?;
            seeds.extend(crate::session::lower_top(&checker, &mut globals, &top));
        }
        SESSIONS.with(|ss| ss.borrow_mut().push(State { checker, globals, generation: 0, seeds: std::mem::take(&mut seeds) }));
        rt.heap.obj_set(s, S_INDEX, Value::fixnum(i as i64));
        i
    };
    Ok(SESSIONS.with(|ss| {
        let mut ss = ss.borrow_mut();
        let state = &mut ss[index];
        f(rt, state)
    }))
}

/// `text`, one top-level form, checked and kept.
fn define(c: &mut Checker, text: &str) -> Result<Top, String> {
    let forms = c.read_in(fixpt_read::FileId(0), text).map_err(|e| e.message)?;
    c.top(&forms[0]).map_err(|e| e.message)
}

/// `w`, one form, checked against the session's checker and its globals,
/// and lowered, as `then` says, the checker left as it was; or the
/// refusal, placed in the code.
fn tried<T>(rt: &mut Runtime, state: &mut State, w: &Wrapped, then: impl FnOnce(&Checker, &mut Globals, Top) -> T) -> Result<T, Value> {
    let State { checker, globals, .. } = state;
    let forms = match checker.read_in(fixpt_read::FileId(0), &w.whole) {
        Ok(f) if f.len() == 1 => f,
        Ok(_) => return Err(fixpt_runtime::prim::stage_failed(rt, "unread", "the code is not one whole expression", 0, w.len)),
        Err(e) => return Err(fixpt_runtime::prim::stage_failed(rt, "unread", &e.message, w.place(e.span.start), w.place(e.span.end))),
    };
    let mut kept = globals.clone();
    match checker.try_top(&forms[0], |c, r| r.map(|top| then(c, &mut kept, top))) {
        Ok(out) => Ok(out),
        Err(e) => Err(fixpt_runtime::prim::stage_failed(rt, "refused", &e.message, w.place(e.span.start), w.place(e.span.end))),
    }
}

/// Lowered, what `%fx26-session-lower` does with session `s` and the
/// product a form's code is: code staged in it, the datum whose value is
/// the thunk, in a list of one; or, `define`, the pending definition,
/// `(sum ok d)`; or the refusal.
fn lower(rt: &mut Runtime, s: Value, staged: Value, define: bool) -> Result<Value, String> {
    let (mt, e, r, code) = staged_parts(rt, staged).ok_or("this machine cannot stage code")?;
    let text = fixpt_runtime::print::write_value(&rt.heap, code);
    if define {
        return lower_define(rt, s, &mt, &e, code, &text);
    }
    let w = Wrapped::of(format!("(the (subr {e} () {r})\n(lambda ()\n"), &text, "\n))\n", &text, 0);
    let made = seeded(rt, s, &mt, |rt, state| {
        let made = tried(rt, state, &w, |c, g, top| crate::session::lower_top(c, g, &top));
        made.map(|c| {
            let mut code = std::mem::take(&mut state.seeds);
            code.extend(c);
            code
        })
    })?;
    match made {
        Ok(code) => Ok(datum(rt, &code)),
        Err(refused) => Ok(refused),
    }
}

/// `code` as one datum, `(begin form …)`, in a list of one.
fn datum(rt: &mut Runtime, code: &Code) -> Value {
    let form = crate::sx::Sx::call("begin", code.0.iter().cloned());
    let d = sx_value(rt, &form);
    rt.heap.cons(d, Value::NULL)
}

/// A definition checked against session `s`: `code`, `(define name init)`
/// or `(define name type init)`; its type found if not written, and its
/// initializer, unless a `lambda`, checked within `E`; the pending
/// definition, the checker as it was.
fn lower_define(rt: &mut Runtime, s: Value, mt: &str, e: &str, code: Value, text: &str) -> Result<Value, String> {
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
    // The definition as written, checked for its type, then its
    // initializer within `E` (a `lambda`'s making does nothing).
    let whole = Wrapped::of(String::new(), text, "\n", text, 0);
    let ty_text = ty.map(|t| write(rt, t));
    let found = seeded(rt, s, mt, |rt, state| {
        let ty = match &ty_text {
            Some(t) => t.clone(),
            None => match tried(rt, state, &whole, |c, _, top| match top {
                Top::Define { ty, .. } => Some(c.staged_text(ty)),
                _ => None,
            }) {
                Ok(Some(t)) => t,
                Ok(None) => return Err(fixpt_runtime::prim::stage_failed(rt, "malformed", usage, 0, len)),
                Err(refused) => return Err(refused),
            },
        };
        let at = text.find(&init_text).map_or(0, |i| text[..i].chars().count());
        let bounded = Wrapped::of(format!("(the (subr {e} () {ty})\n(lambda ()\n"), &init_text, "\n))\n", text, at);
        if !lambda && let Err(refused) = tried(rt, state, &bounded, |_, _, _| ()) {
            return Err(refused);
        }
        let form = format!("(define {shown} {ty} {init_text})");
        // The form with its type checked too, as it will be committed.
        if let Err(refused) = tried(rt, state, &Wrapped::of(String::new(), &form, "\n", &form, 0), |_, _, _| ()) {
            return Err(refused);
        }
        Ok((ty, form, state.generation))
    })?;
    let (ty, form, generation) = match found {
        Ok(f) => f,
        Err(refused) => return Ok(refused),
    };
    let [name, ty, form] = [&name, &ty, &form].map(|t| rt.heap.make_string(t));
    let d = rt.heap.vector_from(&[s, Value::fixnum(generation), name, ty, form, Value::FALSE]);
    Ok(sum(rt, "ok", d))
}

fn is_pending(rt: &Runtime, d: Value) -> bool {
    rt.heap.is_a(d, fixpt_heap::ObjType::Vector) && rt.heap.obj_len(d) == 6
}

fn text(rt: &Runtime, v: Value) -> String {
    rt.heap.string_to_rust(v)
}

/// `f` of session `s`'s state, if it has one.
fn with_state<T>(rt: &Runtime, s: Value, f: impl FnOnce(&mut State) -> T) -> Option<T> {
    let index = rt.heap.obj_ref(s, S_INDEX).as_fixnum();
    (index >= 0).then(|| SESSIONS.with(|ss| f(&mut ss.borrow_mut()[index as usize])))
}

/// `session-redefines`: `(sum fresh #u)`, or `(sum redefines r)`, `r` a
/// `session-redefinition`: the name, its type and the new one, and the
/// session's definitions that use it.
fn redefines(rt: &mut Runtime, s: Value, d: Value) -> Value {
    if !is_pending(rt, d) {
        return sum(rt, "fresh", Value::UNIT);
    }
    let name = text(rt, rt.heap.obj_ref(d, P_NAME));
    let found = with_state(rt, s, |state| {
        let c = &mut state.checker;
        let sym = c.interner.intern(&name);
        let old = c.global_type(sym)?;
        let users: Vec<String> = c
            .defs
            .iter()
            .filter(|def| def.uses.contains(&sym) && !def.names.contains(&sym))
            .flat_map(|def| def.names.iter().map(|n| c.interner.name(*n).to_string()))
            .collect();
        Some((c.staged_text(old), users))
    })
    .flatten();
    let Some((old, users)) = found else { return sum(rt, "fresh", Value::UNIT) };
    let new = rt.heap.obj_ref(d, P_TYPE);
    let name_v = rt.heap.obj_ref(d, P_NAME);
    let old = rt.heap.make_string(&old);
    let users: Vec<Value> = users.iter().map(|u| rt.heap.make_string(u)).collect();
    let users = rt.heap.list_from(&users);
    let r = rt.heap.make_frozen(PRODUCT, &[name_v, old, new, users]);
    sum(rt, "redefines", r)
}

/// Lowered, `%session-ready`'s work: pending definition `d` committed to
/// `s` as `decision` (a `session-decision`) says, the datum that defines
/// it, and what runs again, in a list of one, for the runtime to give
/// `eval`; or the refusal: stale, or the decision refuses.
fn commit_lower(rt: &mut Runtime, s: Value, d: Value, decision: Value) -> Result<Value, String> {
    if !is_pending(rt, d) || rt.heap.obj_ref(d, P_SESSION) != s {
        return Ok(failed(rt, "stale", "this definition was checked against another session"));
    }
    if rt.heap.obj_ref(d, P_USED) != Value::FALSE {
        return Ok(failed(rt, "stale", "this definition was committed already"));
    }
    let tag = if decision.is_bloblet() { rt.heap.bloblet_slot(decision, 2) } else { Value::FALSE };
    let decision = if tag.is_false() { String::new() } else { rt.heap.symbol_name(tag) };
    let (generation, name, form) = (rt.heap.obj_ref(d, P_GENERATION).as_fixnum(), text(rt, rt.heap.obj_ref(d, P_NAME)), text(rt, rt.heap.obj_ref(d, P_FORM)));
    let done = with_state(rt, s, |state| {
        if state.generation != generation {
            return Err(("stale", "the session changed since this definition was checked: check it again".to_string()));
        }
        let sym = state.checker.interner.intern(&name);
        if state.checker.global_type(sym).is_some() {
            match decision.as_str() {
                "refuse" => return Err(("refused", format!("`{name}` is defined already, and the redefinition was refused"))),
                "rerun" => state.checker.defer_reruns = false,
                _ => state.checker.defer_reruns = true,
            }
        }
        let State { checker, globals, generation, seeds } = state;
        let forms = checker.read_in(fixpt_read::FileId(0), &form).map_err(|e| ("refused", e.message))?;
        let done = checker.top_defining(&forms[0]).map_err(|e| ("refused", e.message));
        checker.defer_reruns = true;
        let done = done?;
        let mut code = std::mem::take(seeds);
        for (top, _) in done.hoisted.iter().chain(&done.run) {
            code.extend(crate::session::lower_top(checker, globals, top));
        }
        *generation += 1;
        Ok(code)
    });
    match done {
        None => Ok(failed(rt, "stale", "this definition was checked against a session with no state")),
        Some(Err((kind, why))) => Ok(failed(rt, kind, &why)),
        Some(Ok(code)) => {
            rt.heap.obj_set(d, P_USED, Value::TRUE);
            Ok(datum(rt, &code))
        }
    }
}
