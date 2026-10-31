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
//! vector `#(m index compiler nothing)`, names its state by its index here,
//! made at its first use, when the module's type is known (`seeded`): a
//! global holding `m`, and one for each of `m`'s values, which the
//! session's own may shadow. Each text it reads is a file of its own, kept,
//! so that a definition run again is compiled from its own text.
//!
//! A form checked in a session (`session-check`) is either: an expression,
//! given back as the procedure that evaluates it, or a definition, pending,
//! for `session-commit!`. Made two ways:
//! - **lowered** (`rs-scheme-vm`): each step's Scheme given back as a
//!   datum, for the runtime to give `eval`, the session's globals named by
//!   a prefix of its own;
//! - **compiled** (the machines of the compilers written in FX-26): by a
//!   compiler of the session's own (the conductor's `make-session-compiler`,
//!   kept in the session's third field), whose globals are the session's,
//!   given what the checker found (`rust_facts`); a commit compiles and
//!   runs the definition, and what runs again, as it is readied, and the
//!   program then runs nothing (the session's fourth field, kept).
//!
//! The evaluator's, not yet: a refusal says so.

use crate::check::Checker;
use crate::lower::Globals;
use crate::rust_facts::FormFacts;
use crate::stage::{staged_parts, sx_value, Wrapped};
use crate::sx::Code;
use crate::top::Top;
use fixpt_heap::Value;
use fixpt_read::{FileId, Syntax};
use fixpt_runtime::Runtime;
use std::cell::RefCell;
use std::collections::HashMap;

const SUM: u8 = fixpt_heap::layout::kind("sum");
const PRODUCT: u8 = fixpt_heap::layout::kind("product");

/// A session's state: its checker, the lowering's names of its globals,
/// how many commits it has had, the Scheme that defines `m`'s values'
/// globals until the first code given `eval` runs it first, and the texts
/// it has read, by file.
struct State {
    checker: Checker,
    globals: Globals,
    generation: i64,
    seeds: Code,
    texts: HashMap<u32, String>,
}

thread_local! {
    static SESSIONS: RefCell<Vec<State>> = const { RefCell::new(Vec::new()) };
}

/// The session's fields, and a pending definition's: `#(session generation
/// name type form used)`, the form `(define name type init)` as text.
const S_MODULE: usize = 0;
const S_INDEX: usize = 1;
const S_COMPILER: usize = 2;
const S_NOTHING: usize = 3;
const P_SESSION: usize = 0;
const P_GENERATION: usize = 1;
const P_NAME: usize = 2;
const P_TYPE: usize = 3;
const P_FORM: usize = 4;
const P_USED: usize = 5;

/// The conductor's entry that makes a session's compiler.
const MAKE_COMPILER: &str = "fx26-native:make-session-compiler";

/// Session operation `op` on `a` (the runtime's `sessions`). The session
/// rooted at `base` meanwhile: compiling collects.
pub fn op(rt: &mut Runtime, op: &str, a: &[Value]) -> Result<Value, String> {
    if !is_session(rt, a[0]) {
        return Err("not a session".to_string());
    }
    let base = rt.heap.push_root(a[0]);
    let out = match op {
        "lower" => lower(rt, base, a[1]),
        "commit-lower" => commit_lower(rt, base, a[1], a[2]),
        "check" => check(rt, base, a[1]),
        "ready" => ready(rt, base, a[1], a[2]),
        "committed" => {
            let name = if is_pending(rt, a[1]) { rt.heap.obj_ref(a[1], P_NAME) } else { rt.heap.make_string("") };
            Ok(sum(rt, "defined", name))
        }
        "redefines" => Ok(redefines(rt, a[0], a[1])),
        _ => Err("this machine cannot keep sessions yet".to_string()),
    };
    rt.heap.pop_roots_to(base);
    out
}

fn is_session(rt: &Runtime, s: Value) -> bool {
    rt.heap.is_a(s, fixpt_heap::ObjType::Vector) && rt.heap.obj_len(s) == 4
}

fn sum(rt: &mut Runtime, tag: &str, v: Value) -> Value {
    let base = rt.heap.push_root(v);
    let tag = rt.heap.intern(tag);
    let v = rt.heap.root_at(base);
    rt.heap.pop_roots_to(base);
    rt.heap.make_frozen(SUM, &[tag, v])
}

fn failed(rt: &mut Runtime, kind: &str, why: &str) -> Value {
    fixpt_runtime::prim::stage_failed(rt, kind, why, 0, 0)
}

/// `f` of the state of the session rooted at `base`, made first if it has
/// none, of module type `mt` (printed whole): the checker given `m` as
/// `stage-module`, and each of `m`'s values as a global of its name. Their
/// Scheme runs before the first code given `eval` (`State::seeds`); or,
/// `compiled`, a compiler is made for the session, `m` put in its global,
/// and theirs compiled and run now.
fn seeded<T>(rt: &mut Runtime, base: usize, mt: &str, compiled: bool, f: impl FnOnce(&mut Runtime, &mut State) -> T) -> Result<T, String> {
    let index = rt.heap.obj_ref(rt.heap.root_at(base), S_INDEX).as_fixnum();
    let index = if index >= 0 {
        index as usize
    } else {
        let i = SESSIONS.with(|ss| ss.borrow().len());
        let native = compiled && crate::stage::flags(rt).is_some_and(|(n, _)| n);
        let mut checker = Checker::with_convention(if native { crate::ast::Conv::Native } else { crate::ast::Conv::Cellular });
        checker.defer_reruns = true;
        // Reading a session's global is reading the session, which its
        // forms' types say (`(read r)`), not part of the code's `E`.
        checker.globals_effects = false;
        let mut state = State { checker, globals: Globals::with_prefix(&format!("fx26-session-{i}:")), generation: 0, seeds: Code::default(), texts: HashMap::new() };
        let module = state.checker.interner.intern("stage-module");
        define(&mut state, &format!("(define stage-module (the {mt} %fasl-value))"))?;
        // The module's own global holds `m` itself, given here, not made.
        let m = rt.heap.obj_ref(rt.heap.root_at(base), S_MODULE);
        if compiled {
            let compiler = compiler(rt, base)?;
            let name = rt.heap.intern("stage-module");
            let made = call(rt, compiler, 2, &[name])?;
            rt.heap.set_bloblet_slot(made, fixpt_heap::layout::cellular::GLOBAL_VALUE, rt.heap.obj_ref(rt.heap.root_at(base), S_MODULE));
        } else {
            let global = state.globals.define(&state.checker, module);
            let sym = rt.heap.intern(&global);
            let slot = rt.heap.symbol_global_slot(sym);
            rt.heap.set_global(slot, m);
        }
        let vals = match state.checker.global_type(module).map(|t| state.checker.arena.get(state.checker.arena.resolve(t)).clone()) {
            Some(crate::ast::Ty::Module { vals, .. }) => vals.iter().map(|(n, _)| state.checker.interner.name(*n).to_string()).collect::<Vec<_>>(),
            _ => return Err("a session's module is not a module".to_string()),
        };
        let mut made = Vec::new();
        for n in vals {
            let n = fixpt_read::escape_symbol(&n);
            let (file, top) = define(&mut state, &format!("(define {n} (with stage-module {n}))"))?;
            if compiled {
                let text = &state.texts[&file.0];
                made.push((text.clone(), FormFacts::of(&state.checker, &[&top], file, text, true)));
            } else {
                let code = crate::session::lower_top(&state.checker, &mut state.globals, &top);
                state.seeds.extend(code);
            }
        }
        for (text, facts) in made {
            compile_run(rt, base, &text, &facts)?.map_err(|why| format!("a session's module's values: {why}"))?;
        }
        SESSIONS.with(|ss| ss.borrow_mut().push(state));
        rt.heap.obj_set(rt.heap.root_at(base), S_INDEX, Value::fixnum(i as i64));
        i
    };
    Ok(SESSIONS.with(|ss| {
        let mut ss = ss.borrow_mut();
        let state = &mut ss[index];
        f(rt, state)
    }))
}

/// `text`, read in a file of the session's own, kept: its forms.
fn read(state: &mut State, text: &str) -> Result<(FileId, Vec<Syntax>), crate::FxError> {
    let file = FileId(state.texts.len() as u32 + 1);
    state.texts.insert(file.0, text.to_string());
    Ok((file, state.checker.read_in(file, text)?))
}

/// `text`, one top-level form, checked and kept.
fn define(state: &mut State, text: &str) -> Result<(FileId, Top), String> {
    let (file, forms) = read(state, text).map_err(|e| e.message)?;
    Ok((file, state.checker.top(&forms[0]).map_err(|e| e.message)?))
}

/// `w`, one form, checked against the session's checker and its globals,
/// and what `then` makes of it (its lowering, or what the checker found),
/// the checker left as it was; or the refusal, placed in the code.
fn tried<T>(rt: &mut Runtime, state: &mut State, w: &Wrapped, then: impl FnOnce(&Checker, &mut Globals, Top, FileId) -> T) -> Result<T, Value> {
    let (file, forms) = match read(state, &w.whole) {
        Ok((file, f)) if f.len() == 1 => (file, f),
        Ok(_) => return Err(fixpt_runtime::prim::stage_failed(rt, "unread", "the code is not one whole expression", 0, w.len)),
        Err(e) => return Err(fixpt_runtime::prim::stage_failed(rt, "unread", &e.message, w.place(e.span.start), w.place(e.span.end))),
    };
    let mut kept = state.globals.clone();
    match state.checker.try_top(&forms[0], |c, r| r.map(|top| then(c, &mut kept, top, file))) {
        Ok(out) => Ok(out),
        Err(e) => Err(fixpt_runtime::prim::stage_failed(rt, "refused", &e.message, w.place(e.span.start), w.place(e.span.end))),
    }
}

/// Whether `code` is a definition, `(define …)`.
fn is_definition(rt: &Runtime, code: Value) -> bool {
    let head = if code.is_pair() { rt.heap.car(code) } else { Value::NULL };
    rt.heap.is_a(head, fixpt_heap::ObjType::Symbol) && rt.heap.symbol_name(head) == "define"
}

/// An expression, `text`, as it is checked: within `E`, of type `R`.
fn expression(e: &str, r: &str, text: &str) -> Wrapped {
    Wrapped::of(format!("(the (subr {e} () {r})\n(lambda ()\n"), text, "\n))\n", text, 0)
}

/// Lowered, what `%fx26-session-lower` does with the session at `base` and
/// the product a form's code is: an expression, the datum whose value is the
/// procedure that evaluates it, in a list of one; a definition, `(sum ok
/// (sum definition d))`, `d` pending; or the refusal.
fn lower(rt: &mut Runtime, base: usize, staged: Value) -> Result<Value, String> {
    let (mt, e, r, code) = staged_parts(rt, staged).ok_or("this machine cannot stage code")?;
    let text = fixpt_runtime::print::write_value(&rt.heap, code);
    if is_definition(rt, code) {
        return check_define(rt, base, &mt, &e, code, &text, false);
    }
    let w = expression(&e, &r, &text);
    let made = seeded(rt, base, &mt, false, |rt, state| {
        let made = tried(rt, state, &w, |c, g, top, _| crate::session::lower_top(c, g, &top));
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

/// Compiled, what `%fx26-session-check` does: an expression, the procedure
/// that evaluates it, `(sum ok (sum expression p))`; a definition, pending;
/// or the refusal.
fn check(rt: &mut Runtime, base: usize, staged: Value) -> Result<Value, String> {
    let (mt, e, r, code) = staged_parts(rt, staged).ok_or("this machine cannot stage code")?;
    let text = fixpt_runtime::print::write_value(&rt.heap, code);
    if is_definition(rt, code) {
        return check_define(rt, base, &mt, &e, code, &text, true);
    }
    let w = expression(&e, &r, &text);
    let found = seeded(rt, base, &mt, true, |rt, state| tried(rt, state, &w, |c, _, top, file| FormFacts::of(c, &[&top], file, &w.whole, true)))?;
    let facts = match found {
        Ok(facts) => facts,
        Err(refused) => return Ok(refused),
    };
    match compile_run(rt, base, &w.whole, &facts)? {
        Ok(p) => {
            let p = sum(rt, "expression", p);
            Ok(sum(rt, "ok", p))
        }
        Err(why) => Ok(failed(rt, "refused", &why)),
    }
}

/// `code` as one datum, `(begin form …)`, in a list of one.
fn datum(rt: &mut Runtime, code: &Code) -> Value {
    let form = crate::sx::Sx::call("begin", code.0.iter().cloned());
    let d = sx_value(rt, &form);
    rt.heap.cons(d, Value::NULL)
}

/// A definition checked against the session at `base`: `code`, `(define
/// name init)` or `(define name type init)`; its type found if not
/// written, and its initializer, unless a `lambda`, checked within `E`;
/// the pending definition, `(sum ok (sum definition d))`, the checker as
/// it was.
fn check_define(rt: &mut Runtime, base: usize, mt: &str, e: &str, code: Value, text: &str, compiled: bool) -> Result<Value, String> {
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
    let found = seeded(rt, base, mt, compiled, |rt, state| {
        let ty = match &ty_text {
            Some(t) => t.clone(),
            None => match tried(rt, state, &whole, |c, _, top, _| match top {
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
        if !lambda && let Err(refused) = tried(rt, state, &bounded, |_, _, _, _| ()) {
            return Err(refused);
        }
        let form = format!("(define {shown} {ty} {init_text})");
        // The form with its type checked too, as it will be committed.
        if let Err(refused) = tried(rt, state, &Wrapped::of(String::new(), &form, "\n", &form, 0), |_, _, _, _| ()) {
            return Err(refused);
        }
        Ok((ty, form, state.generation))
    })?;
    let (ty, form, generation) = match found {
        Ok(f) => f,
        Err(refused) => return Ok(refused),
    };
    let [name, ty, form] = [&name, &ty, &form].map(|t| rt.heap.make_string(t));
    let s = rt.heap.root_at(base);
    let d = rt.heap.vector_from(&[s, Value::fixnum(generation), name, ty, form, Value::FALSE]);
    let d = sum(rt, "definition", d);
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

/// Pending definition `d` committed to the session at `base`, as
/// `decision` (a `session-decision`) says: by the checker, and what each
/// form that runs, the definition and those run again, is made of
/// (`then`, of each form's text, its file, and its checked tree); or why
/// not: stale, or the decision refuses.
fn committed<T>(
    rt: &mut Runtime,
    base: usize,
    d: Value,
    decision: Value,
    mut then: impl FnMut(&Checker, &mut Globals, &str, FileId, &Top) -> T,
) -> Result<(Vec<T>, Code), (&'static str, String)> {
    let s = rt.heap.root_at(base);
    if !is_pending(rt, d) || rt.heap.obj_ref(d, P_SESSION) != s {
        return Err(("stale", "this definition was checked against another session".to_string()));
    }
    if rt.heap.obj_ref(d, P_USED) != Value::FALSE {
        return Err(("stale", "this definition was committed already".to_string()));
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
        let (_, forms) = read(state, &form).map_err(|e| ("refused", e.message))?;
        let done = state.checker.top_defining(&forms[0]).map_err(|e| ("refused", e.message));
        state.checker.defer_reruns = true;
        let done = done?;
        let mut made = Vec::new();
        let State { checker, globals, generation, seeds, texts } = state;
        for (top, _) in done.hoisted.iter().chain(&done.run) {
            let exp = match top {
                Top::Define { exp, .. } | Top::Exp(crate::check::Checked { exp, .. }) => Some(*exp),
                Top::DefineRec { bindings, .. } => bindings.first().map(|(_, _, e)| *e),
                _ => None,
            };
            let Some(exp) = exp else { continue };
            let file = checker.arena.span_of(exp).file;
            let text = texts.get(&file.0).map(String::as_str).unwrap_or("");
            made.push(then(checker, globals, text, file, top));
        }
        *generation += 1;
        Ok((made, std::mem::take(seeds)))
    });
    match done {
        None => Err(("stale", "this definition was checked against a session with no state".to_string())),
        Some(Err(e)) => Err(e),
        Some(Ok(out)) => {
            rt.heap.obj_set(d, P_USED, Value::TRUE);
            Ok(out)
        }
    }
}

/// Lowered, `%session-ready`'s work: the datum that defines `d`, and what
/// runs again, in a list of one, for the runtime to give `eval`; or the
/// refusal.
fn commit_lower(rt: &mut Runtime, base: usize, d: Value, decision: Value) -> Result<Value, String> {
    match committed(rt, base, d, decision, |c, g, _, _, top| crate::session::lower_top(c, g, top)) {
        Ok((made, mut code)) => {
            for c in made {
                code.extend(c);
            }
            Ok(datum(rt, &code))
        }
        Err((kind, why)) => Ok(failed(rt, kind, &why)),
    }
}

/// Compiled, `%session-ready`: `d` committed, each form that runs compiled
/// and run now, by the session's compiler, a definition every use can take
/// keeping its global; then `(sum go p)`, `p` doing nothing, for the
/// program to run; or the refusal.
fn ready(rt: &mut Runtime, base: usize, d: Value, decision: Value) -> Result<Value, String> {
    let made = committed(rt, base, d, decision, |c, _, text, file, top| {
        let keeps = match top {
            Top::Define { name, assigns: true, .. } => vec![c.interner.name(*name).to_string()],
            Top::DefineRec { bindings, assigns: true } => bindings.iter().map(|(n, _, _)| c.interner.name(*n).to_string()).collect(),
            _ => Vec::new(),
        };
        (text.to_string(), FormFacts::of(c, &[top], file, text, true), keeps)
    });
    let made = match made {
        Ok((made, _)) => made,
        Err((kind, why)) => return Ok(failed(rt, kind, &why)),
    };
    for (text, facts, keeps) in made {
        for k in keeps {
            let compiler = compiler(rt, base)?;
            let k = rt.heap.intern(&k);
            call(rt, compiler, 3, &[k])?;
        }
        if let Err(why) = compile_run(rt, base, &text, &facts)? {
            return Ok(failed(rt, "refused", &why));
        }
    }
    let p = nothing(rt, base)?;
    Ok(sum(rt, "go", p))
}

/// The procedure of no arguments that does nothing, made once for the
/// session at `base` (its fourth field).
fn nothing(rt: &mut Runtime, base: usize) -> Result<Value, String> {
    let s = rt.heap.root_at(base);
    let p = rt.heap.obj_ref(s, S_NOTHING);
    if p != Value::FALSE {
        return Ok(p);
    }
    let w = Wrapped::of(String::new(), "(lambda () #u)", "\n", "", 0);
    let index = rt.heap.obj_ref(s, S_INDEX).as_fixnum() as usize;
    let found = SESSIONS.with(|ss| tried(rt, &mut ss.borrow_mut()[index], &w, |c, _, top, file| FormFacts::of(c, &[&top], file, &w.whole, true)));
    let facts = found.map_err(|_| "a session's procedure of nothing does not check".to_string())?;
    let p = compile_run(rt, base, &w.whole, &facts)?.map_err(|why| format!("a session's procedure of nothing: {why}"))?;
    let s = rt.heap.root_at(base);
    rt.heap.obj_set(s, S_NOTHING, p);
    Ok(p)
}

/// The session at `base`'s compiler, made at its first use (its third
/// field): the product the conductor's `make-session-compiler` makes.
fn compiler(rt: &mut Runtime, base: usize) -> Result<Value, String> {
    let s = rt.heap.root_at(base);
    let c = rt.heap.obj_ref(s, S_COMPILER);
    if c != Value::FALSE {
        return Ok(c);
    }
    let make = crate::stage::global(rt, MAKE_COMPILER).ok_or("this machine cannot keep sessions: its front end is not compiled")?;
    let c = fixpt_runtime::prim::call_front_end(rt, make, &[])?;
    let s = rt.heap.root_at(base);
    rt.heap.obj_set(s, S_COMPILER, c);
    Ok(c)
}

/// Entry `i` (from 1) of the session's compiler, `compiler`, called with
/// `args`: its value.
fn call(rt: &mut Runtime, compiler: Value, i: usize, args: &[Value]) -> Result<Value, String> {
    let f = rt.heap.bloblet_slot(compiler, i + 1);
    let fuel = std::mem::replace(&mut rt.word_fuel, u64::MAX);
    let out = fixpt_runtime::prim::call_front_end(rt, f, args);
    rt.word_fuel = fuel;
    out
}

/// `text`, a session's form, compiled by the session at `base`'s compiler,
/// given what the checker found of it, and its word run: the value; or
/// why the compiler would not.
fn compile_run(rt: &mut Runtime, base: usize, text: &str, facts: &FormFacts) -> Result<Result<Value, String>, String> {
    let (native, registers) = crate::stage::flags(rt).ok_or("this machine cannot keep sessions")?;
    let compiler = compiler(rt, base)?;
    let mark = rt.heap.push_root(compiler);
    let t = rt.heap.make_string(text);
    rt.heap.push_root(t);
    let f = facts.facts(&mut rt.heap);
    rt.heap.push_root(f);
    let w = facts.withs(&mut rt.heap);
    rt.heap.push_root(w);
    let r = facts.reshapes(&mut rt.heap);
    let [compiler, t, f, w] = [0, 1, 2, 3].map(|i| rt.heap.root_at(mark + i));
    rt.heap.pop_roots_to(mark);
    let made = call(rt, compiler, 1, &[t, f, w, r, Value::boolean(native), Value::boolean(registers)])?;
    let tag = rt.heap.bloblet_slot(made, 2);
    let payload = rt.heap.bloblet_slot(made, 3);
    if tag != rt.heap.intern("made") {
        return Ok(Err(rt.heap.string_to_rust(payload)));
    }
    let run = rt.run_word.ok_or("no cellular machine is installed")?;
    run(rt, payload, &[]).map(Ok)
}
