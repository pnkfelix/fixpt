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
//! vector `#(m index front-end texts)`, names its state by its index here,
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
//!   given what the checker found (`rust_facts`); a commit compiles the
//!   definition, and what runs again, as it is readied, into the procedure
//!   the program then calls to run them;
//! - **evaluated** (`fx-ast-eval`): each step's forms given back as text,
//!   for the evaluator to run in the session's environment, which it keeps
//!   (`eval-core.fx`'s `ev-session-…`), `m`'s as `stage-module`.

use crate::check::Checker;
use crate::lower::Globals;
use crate::rust_facts::FormFacts;
use crate::stage::{staged_parts, sx_value, Parts, Wrapped};
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
/// how many commits it has had, what defines `m`'s values' globals until
/// the first step runs it first (as Scheme, lowered; as text, evaluated),
/// the texts it has read, by file (tries among them), and the reading of
/// the last its checker kept.
struct State {
    checker: Checker,
    globals: Globals,
    generation: i64,
    seeds: Code,
    seed_texts: Vec<String>,
    texts: HashMap<u32, String>,
    /// The session's state as its checker kept it (the standard
    /// environment's as it begins, `ids::standard_state`): the
    /// state after the last text kept, each form read in the state the one
    /// before left (`ids::forms_state`; `docs/research/loads-and-places.md`,
    /// "Decided: three keys"). A try leaves it as it was.
    kept: i64,
}

impl State {
    /// What the session's compiler reads a text in (`session-compile`): the
    /// state kept, and the switches its checker is set to now.
    fn keys(&self) -> (i64, String) {
        (self.kept, crate::ids::Settings::of(&self.checker).text())
    }

    /// `text` kept by the checker, as it was set when it checked it.
    fn keep(&mut self, settings: &crate::ids::Settings, text: &str) {
        self.kept = crate::ids::forms_state(self.kept, settings, text, &[]).unwrap_or(self.kept);
    }
}

/// How a session's steps are made (the module's header).
#[derive(Clone, Copy, PartialEq)]
enum Mode {
    Lowered,
    Compiled,
    Evaluated,
}

thread_local! {
    static SESSIONS: RefCell<Vec<State>> = const { RefCell::new(Vec::new()) };
}

/// The session's fields, and a pending definition's: `#(session generation
/// name type form used)`, the form `(define name type init)` as text.
const S_MODULE: usize = 0;
const S_INDEX: usize = 1;
const S_COMPILER: usize = 2;
pub(crate) const P_SESSION: usize = 0;
pub(crate) const P_GENERATION: usize = 1;
pub(crate) const P_NAME: usize = 2;
pub(crate) const P_TYPE: usize = 3;
pub(crate) const P_FORM: usize = 4;
pub(crate) const P_USED: usize = 5;
/// The type's rep (a bytevector of its binary form), where the session's
/// checker made one, and the form naming it `%stage-type`, which its
/// commit checks (`sessions26.rs`; `docs/research/heap-types.md`, step 4);
/// `#f` and `#f` if not.
pub(crate) const P_REP: usize = 6;
pub(crate) const P_REP_FORM: usize = 7;

/// The conductor's entry that makes a session's compiler.
const MAKE_COMPILER: &str = "fx26-native:make-session-compiler";

/// Session operation `op` on `a` (the runtime's `sessions`). The session
/// rooted at `base` meanwhile: compiling collects.
pub fn op(rt: &mut Runtime, op: &str, a: &[Value]) -> Result<Value, String> {
    if !is_session(rt, a[0]) {
        return Err("not a session".to_string());
    }
    let base = rt.heap.push_root(a[0]);
    // On the machines of the compilers written in FX-26, a session is the
    // checker written in FX-26's (`sessions26.rs`).
    let on26 = |rt: &mut Runtime| crate::sessions26::takes(rt, a[0]);
    let out = match op {
        "lower" => lower(rt, base, a[1], a[2]),
        "commit-lower" => commit_lower(rt, base, a[1], a[2]),
        "check" if on26(rt) => crate::sessions26::check(rt, base, a[1], a[2]),
        "check" => check(rt, base, a[1], a[2]),
        "eval-check" if crate::sessions26::takes(rt, a[0]) => crate::sessions26::eval_check(rt, base, &a[1..]),
        "eval-check" => eval_check(rt, base, &a[1..]),
        "eval-ready" if rt.heap.obj_ref(a[0], S_INDEX).as_fixnum() <= -2 => {
            let decision = text(rt, a[2]);
            crate::sessions26::ready(rt, base, a[1], &decision, true)
        }
        "eval-ready" => eval_ready(rt, base, a[1], a[2]),
        "ready" if rt.heap.obj_ref(a[0], S_INDEX).as_fixnum() <= -2 => {
            let decision = decided(rt, a[2]);
            crate::sessions26::ready(rt, base, a[1], &decision, false)
        }
        "ready" => ready(rt, base, a[1], a[2]),
        "redefines" if rt.heap.obj_ref(a[0], S_INDEX).as_fixnum() <= -2 => crate::sessions26::redefines(rt, base, a[1]),
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

pub(crate) fn sum(rt: &mut Runtime, tag: &str, v: Value) -> Value {
    let base = rt.heap.push_root(v);
    let tag = rt.heap.intern(tag);
    let v = rt.heap.root_at(base);
    rt.heap.pop_roots_to(base);
    rt.heap.make_frozen(SUM, &[tag, v])
}

pub(crate) fn failed(rt: &mut Runtime, kind: &str, why: &str) -> Value {
    fixpt_runtime::prim::stage_failed(rt, kind, why, 0, 0)
}

/// `f` of the state of the session rooted at `base`, made first if it has
/// none, of module type `mt` (printed whole): the checker given `m` as
/// `stage-module`, and each of `m`'s values as a global of its name. Their
/// Scheme runs before the first code given `eval` (`State::seeds`); or,
/// compiled, a compiler is made for the session, `m` put in its global,
/// and theirs compiled and run now; or, evaluated, their texts run before
/// the first step's (`State::seed_texts`), the evaluator binding `m`.
fn seeded<T>(rt: &mut Runtime, base: usize, parts: &Parts, mode: Mode, f: impl FnOnce(&mut Runtime, &mut State) -> T) -> Result<T, String> {
    // Its types by rep, each named for the step (`stage::step_reps`;
    // `docs/research/heap-types.md`, step 6); its callers refuse a step
    // with none (`step_reps_of`).
    let reps = parts.rep.as_deref().and_then(crate::stage::step_reps);
    let mt = crate::stage::MODULE_TYPE;
    let index = rt.heap.obj_ref(rt.heap.root_at(base), S_INDEX).as_fixnum();
    let index = if index >= 0 {
        index as usize
    } else {
        let i = SESSIONS.with(|ss| ss.borrow().len());
        let compiled = mode == Mode::Compiled;
        let native = compiled && crate::stage::flags(rt).is_some_and(|(n, _)| n);
        let mut checker = Checker::with_convention(if native { crate::ast::Conv::Native } else { crate::ast::Conv::Cellular });
        checker.defer_reruns = true;
        // Reading a session's global is reading the session, which its
        // forms' types say (`(read r)`), not part of the code's `E`.
        checker.globals_effects = false;
        let mut state = State { checker, globals: Globals::with_prefix(&format!("fx26-session-{i}:")), generation: 0, seeds: Code::default(), seed_texts: Vec::new(), texts: HashMap::new(), kept: crate::ids::standard_state() };
        let module = state.checker.interner.intern("stage-module");
        let depth = bind_step_names(&mut state.checker, reps.as_ref());
        let seed = define(&mut state, &format!("(define stage-module (the {mt} %fasl-value))"));
        state.checker.dscope.truncate(depth);
        seed?;
        // The module's own global holds `m` itself, given here, not made.
        let m = rt.heap.obj_ref(rt.heap.root_at(base), S_MODULE);
        if compiled {
            let compiler = compiler(rt, base)?;
            let name = rt.heap.intern("stage-module");
            let made = call(rt, compiler, 2, &[name])?;
            rt.heap.set_bloblet_slot(made, fixpt_heap::layout::cellular::GLOBAL_VALUE, rt.heap.obj_ref(rt.heap.root_at(base), S_MODULE));
        } else if mode == Mode::Lowered {
            let global = state.globals.define(&state.checker, module);
            let sym = rt.heap.intern(&global);
            let slot = rt.heap.symbol_global_slot(sym);
            rt.heap.set_global(slot, m);
        }
        let vals = match state.checker.global_type(module).map(|t| state.checker.arena.get(state.checker.arena.resolve(t)).clone()) {
            Some(crate::ast::Ty::Module { vals, .. }) => vals.iter().map(|(n, _)| state.checker.interner.name(*n).to_string()).collect::<Vec<_>>(),
            _ => return Err("a session's module is not a module".to_string()),
        };
        // Its types and effects, each named as an `import` names them; they
        // make no code.
        for d in reps.as_ref().map(|r| r.descs.clone()).unwrap_or_default() {
            define(&mut state, &crate::stage::desc_defines(&[d]))?;
        }
        // Each linked now to what it names, as a module's aliases are when it
        // is bound: else a step's trial would link one to an abstract type's
        // node of its own, which the trial's end takes back.
        state.checker.link_aliases(module);
        let mut made = Vec::new();
        for n in vals {
            let n = fixpt_read::escape_symbol(&n);
            let (file, top) = define(&mut state, &format!("(define {n} (with stage-module {n}))"))?;
            let text = &state.texts[&file.0];
            if compiled {
                made.push((text.clone(), FormFacts::of(&state.checker, &[&top], file, text, true)));
            } else if mode == Mode::Evaluated {
                state.seed_texts.push(text.clone());
            } else {
                let code = crate::session::lower_top(&state.checker, &mut state.globals, &top);
                state.seeds.extend(code);
            }
        }
        for (text, facts) in made {
            compile_run(rt, base, Some(&mut state), None, &text, &facts, false)?.map_err(|why| format!("a session's module's values: {why}"))?;
        }
        SESSIONS.with(|ss| ss.borrow_mut().push(state));
        rt.heap.obj_set(rt.heap.root_at(base), S_INDEX, Value::fixnum(i as i64));
        i
    };
    Ok(SESSIONS.with(|ss| {
        let mut ss = ss.borrow_mut();
        let state = &mut ss[index];
        let depth = bind_step_names(&mut state.checker, reps.as_ref());
        let out = f(rt, state);
        state.checker.dscope.truncate(depth);
        out
    }))
}

/// The names a step's text gives its types (`stage::StepReps`), each bound
/// in checker `c` to its rep imported; how deep its description scope was
/// before, to which the caller cuts it back after the step.
fn bind_step_names(c: &mut Checker, reps: Option<&crate::stage::StepReps>) -> usize {
    let depth = c.dscope.len();
    for (n, bytes) in reps.map(|r| r.named.as_slice()).unwrap_or_default() {
        let Ok(rep) = fixpt_reps::binary::decode(bytes, fixpt_reps::heap::validate_all()) else { continue };
        let d = match c.import_desc(&rep) {
            Ok(crate::ast::D::Effect(e)) => crate::parse::DScope::Eff(e),
            Ok(crate::ast::D::Type(t)) => crate::parse::DScope::Rec(t),
            _ => continue,
        };
        let n = c.interner.intern(n);
        c.dscope.push((n, d));
    }
    depth
}

/// Whether `parts` has its types by rep, as a step's (`stage::step_reps`):
/// a step without is refused (`stage::no_rep`).
fn has_step_reps(parts: &Parts) -> bool {
    parts.rep.as_deref().and_then(crate::stage::step_reps).is_some()
}

/// An expression step's code wrapped, its type named (`%stage-result-type`,
/// `(subr E () R)`).
pub(crate) fn step_expression(text: &str) -> Wrapped {
    let r = crate::stage::RESULT_TYPE;
    Wrapped::of(format!("(the {r}\n(lambda ()\n"), text, "\n))\n", text, 0)
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
    let settings = crate::ids::Settings::of(&state.checker);
    let top = state.checker.top(&forms[0]).map_err(|e| e.message)?;
    state.keep(&settings, text);
    Ok((file, top))
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
pub(crate) fn is_definition(rt: &Runtime, code: Value) -> bool {
    let head = if code.is_pair() { rt.heap.car(code) } else { Value::NULL };
    rt.heap.is_a(head, fixpt_heap::ObjType::Symbol) && rt.heap.symbol_name(head) == "define"
}


/// Lowered, what `%fx26-session-lower` does with the session at `base` and
/// the product a form's code is: an expression, the datum whose value is the
/// procedure that evaluates it, in a list of one; a definition, `(sum ok
/// (sum definition d))`, `d` pending; or the refusal.
fn lower(rt: &mut Runtime, base: usize, staged: Value, given: Value) -> Result<Value, String> {
    let (parts, code) = staged_parts(rt, staged, given).ok_or("this machine cannot stage code")?;
    if !has_step_reps(&parts) {
        return Ok(crate::stage::no_rep(rt));
    }
    let text = fixpt_runtime::print::write_value(&rt.heap, code);
    if is_definition(rt, code) {
        return check_define(rt, base, &parts, code, &text, Mode::Lowered);
    }
    let w = step_expression(&text);
    let made = seeded(rt, base, &parts, Mode::Lowered, |rt, state| {
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
fn check(rt: &mut Runtime, base: usize, staged: Value, given: Value) -> Result<Value, String> {
    let (parts, code) = staged_parts(rt, staged, given).ok_or("this machine cannot stage code")?;
    if !has_step_reps(&parts) {
        return Ok(crate::stage::no_rep(rt));
    }
    let text = fixpt_runtime::print::write_value(&rt.heap, code);
    if is_definition(rt, code) {
        return check_define(rt, base, &parts, code, &text, Mode::Compiled);
    }
    let w = step_expression(&text);
    let found = seeded(rt, base, &parts, Mode::Compiled, |rt, state| tried(rt, state, &w, |c, _, top, file| FormFacts::of(c, &[&top], file, &w.whole, true)))?;
    let facts = match found {
        Ok(facts) => facts,
        Err(refused) => return Ok(refused),
    };
    match compile_run(rt, base, None, parts.rep.as_deref(), &w.whole, &facts, false)? {
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
fn check_define(rt: &mut Runtime, base: usize, against: &Parts, code: Value, text: &str, mode: Mode) -> Result<Value, String> {
    let e = crate::stage::EFFECT;
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
    let found = seeded(rt, base, against, mode, |rt, state| {
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
    let d = pending(rt, base, generation, &name, &ty, &form, None);
    let d = sum(rt, "definition", d);
    Ok(sum(rt, "ok", d))
}

/// A pending definition of the session at `base`, checked at `generation`:
/// `#(session generation name type form used rep rep-form)`, its strings
/// made rooted; `by_rep`, its type's rep and the form that names it.
pub(crate) fn pending(rt: &mut Runtime, base: usize, generation: i64, name: &str, ty: &str, form: &str, by_rep: Option<(&[u8], &str)>) -> Value {
    let mark = rt.heap.push_root(Value::FALSE);
    for t in [name, ty, form] {
        let v = rt.heap.make_string(t);
        rt.heap.push_root(v);
    }
    let (rep, rep_form) = match by_rep {
        Some((bytes, checked)) => {
            let b = rt.heap.make_bytevector(bytes);
            rt.heap.push_root(b);
            let f = rt.heap.make_string(checked);
            rt.heap.push_root(f);
            (rt.heap.root_at(mark + 4), rt.heap.root_at(mark + 5))
        }
        None => (Value::FALSE, Value::FALSE),
    };
    let [name, ty, form] = [1, 2, 3].map(|i| rt.heap.root_at(mark + i));
    let s = rt.heap.root_at(base);
    let d = rt.heap.vector_from(&[s, Value::fixnum(generation), name, ty, form, Value::FALSE, rep, rep_form]);
    rt.heap.pop_roots_to(mark);
    d
}

pub(crate) fn is_pending(rt: &Runtime, d: Value) -> bool {
    rt.heap.is_a(d, fixpt_heap::ObjType::Vector) && rt.heap.obj_len(d) == 8
}

pub(crate) fn text(rt: &Runtime, v: Value) -> String {
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
/// (`then`, of each form's text, its file, and its checked tree), and what
/// defines `m`'s values, if nothing has run it yet; or why not: stale, or
/// the decision (its tag, as text) refuses.
fn committed<T>(
    rt: &mut Runtime,
    base: usize,
    d: Value,
    decision: &str,
    mut then: impl FnMut(&Checker, &mut Globals, &str, FileId, &Top) -> T,
) -> Result<(Vec<T>, Code, Vec<String>), (&'static str, String)> {
    let s = rt.heap.root_at(base);
    if !is_pending(rt, d) || rt.heap.obj_ref(d, P_SESSION) != s {
        return Err(("stale", "this definition was checked against another session".to_string()));
    }
    if rt.heap.obj_ref(d, P_USED) != Value::FALSE {
        return Err(("stale", "this definition was committed already".to_string()));
    }
    let (generation, name, form) = (rt.heap.obj_ref(d, P_GENERATION).as_fixnum(), text(rt, rt.heap.obj_ref(d, P_NAME)), text(rt, rt.heap.obj_ref(d, P_FORM)));
    let done = with_state(rt, s, |state| {
        if state.generation != generation {
            return Err(("stale", "the session changed since this definition was checked: check it again".to_string()));
        }
        let sym = state.checker.interner.intern(&name);
        if state.checker.global_type(sym).is_some() {
            match decision {
                "refuse" => return Err(("refused", format!("`{name}` is defined already, and the redefinition was refused"))),
                "rerun" => state.checker.defer_reruns = false,
                _ => state.checker.defer_reruns = true,
            }
        }
        let (_, forms) = read(state, &form).map_err(|e| ("refused", e.message.into()))?;
        let settings = crate::ids::Settings::of(&state.checker);
        let done = state.checker.top_defining(&forms[0]).map_err(|e| ("refused", String::from(e.message)));
        state.checker.defer_reruns = true;
        let done = done?;
        state.keep(&settings, &form);
        let mut made = Vec::new();
        let State { checker, globals, generation, seeds, seed_texts, texts, .. } = state;
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
        Ok((made, std::mem::take(seeds), std::mem::take(seed_texts)))
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
    let decision = decided(rt, decision);
    match committed(rt, base, d, &decision, |c, g, _, _, top| crate::session::lower_top(c, g, top)) {
        Ok((made, mut code, _)) => {
            for c in made {
                code.extend(c);
            }
            Ok(datum(rt, &code))
        }
        Err((kind, why)) => Ok(failed(rt, kind, &why)),
    }
}

/// Compiled, `%session-ready`: `d` committed, and the forms that run, the
/// definition's and those run again, compiled by the session's compiler as
/// one text, into the procedure that runs them (`compile-deferred`), a
/// definition every use can take keeping its global; then `(sum go p)`,
/// for the program to call; or the refusal.
fn ready(rt: &mut Runtime, base: usize, d: Value, decision: Value) -> Result<Value, String> {
    let decision = decided(rt, decision);
    let made = committed(rt, base, d, &decision, |c, _, text, file, top| (text.to_string(), FormFacts::of(c, &[top], file, text, true), keeps(c, top)));
    let made = match made {
        Ok((made, _, _)) => made,
        Err((kind, why)) => return Ok(failed(rt, kind, &why)),
    };
    let (mut whole, mut all) = (String::new(), FormFacts::none());
    for (text, facts, keeps) in made {
        for k in keeps {
            let compiler = compiler(rt, base)?;
            let k = rt.heap.intern(&k);
            call(rt, compiler, 3, &[k])?;
        }
        all = all.and_after(facts, whole.chars().count() as i64);
        whole.push_str(&text);
        whole.push('\n');
    }
    match compile_run(rt, base, None, None, &whole, &all, true)? {
        Ok(p) => Ok(sum(rt, "go", p)),
        Err(why) => Ok(failed(rt, "refused", &why)),
    }
}

/// A `session-decision`'s tag, as text; none if it is not one.
pub(crate) fn decided(rt: &Runtime, decision: Value) -> String {
    let tag = if decision.is_bloblet() { rt.heap.sum_tag(decision) } else { Value::FALSE };
    if tag.is_false() { String::new() } else { rt.heap.symbol_name(tag) }
}

/// The names whose globals `top`, run again, assigns: those a definition
/// every use can take keeps.
fn keeps(c: &Checker, top: &Top) -> Vec<String> {
    match top {
        Top::Define { name, assigns: true, .. } => vec![c.interner.name(*name).to_string()],
        Top::DefineRec { bindings, assigns: true } => bindings.iter().map(|(n, _, _)| c.interner.name(*n).to_string()).collect(),
        _ => Vec::new(),
    }
}

/// Evaluated, what `%fx26-session-eval-check` does with the session at
/// `base`, the code as text, the names of the variables its type names,
/// that type as a rep and the evidence's reps' binary forms (`a`): an
/// expression, `(sum run texts)`, the forms to run, the
/// last's value the procedure that evaluates it; a definition, pending;
/// or the refusal.
fn eval_check(rt: &mut Runtime, base: usize, a: &[Value]) -> Result<Value, String> {
    let text = self::text(rt, a[0]);
    let given = fixpt_runtime::evidence::Given::of_bytes(rt, a[1], a[3]);
    let parts = Parts { rep: crate::stage::given_rep(rt, a[2], &given) };
    if !has_step_reps(&parts) {
        return Ok(crate::stage::no_rep(rt));
    }
    let mut interner = std::mem::take(&mut rt.interner);
    let read = fixpt_read::Reader::new(&text, FileId(0), fixpt_read::SyntaxProfile::FX91, &mut interner).read_all();
    rt.interner = interner;
    let code = match read.as_deref() {
        Ok([one]) => fixpt_runtime::port::syntax_to_value(rt, one),
        Ok(_) => return Ok(failed(rt, "unread", "the code is not one whole expression")),
        Err(e) => return Ok(failed(rt, "unread", &e.message)),
    };
    if is_definition(rt, code) {
        return check_define(rt, base, &parts, code, &text, Mode::Evaluated);
    }
    let w = step_expression(&text);
    let made = seeded(rt, base, &parts, Mode::Evaluated, |rt, state| {
        tried(rt, state, &w, |_, _, _, _| ()).map(|()| {
            let mut texts = std::mem::take(&mut state.seed_texts);
            texts.push(w.whole.clone());
            texts
        })
    })?;
    match made {
        Ok(texts) => {
            let list = strings(rt, texts.iter().map(|t| (t.as_str(), None)));
            Ok(sum(rt, "run", list))
        }
        Err(refused) => Ok(refused),
    }
}

/// `texts` as a list of strings; each given a flag, of the product of it
/// and its flag.
pub(crate) fn strings<'a>(rt: &mut Runtime, texts: impl DoubleEndedIterator<Item = (&'a str, Option<bool>)>) -> Value {
    let base = rt.heap.push_root(Value::NULL);
    for (t, flag) in texts.rev() {
        let mut v = rt.heap.make_string(t);
        if let Some(flag) = flag {
            v = rt.heap.make_frozen(PRODUCT, &[v, Value::boolean(flag)]);
        }
        let rest = rt.heap.root_at(base);
        let list = rt.heap.cons(v, rest);
        rt.heap.set_root_at(base, list);
    }
    let list = rt.heap.root_at(base);
    rt.heap.pop_roots_to(base);
    list
}

/// Evaluated, `%session-ready`'s work: `d` committed as `decision` (its
/// tag, as text) says; then `(sum run forms)`, each form's text and
/// whether it keeps its globals, for the evaluator to run in the session;
/// or the refusal.
fn eval_ready(rt: &mut Runtime, base: usize, d: Value, decision: Value) -> Result<Value, String> {
    let decision = text(rt, decision);
    let made = committed(rt, base, d, &decision, |c, _, text, _, top| (text.to_string(), !keeps(c, top).is_empty()));
    let (made, _, seeds) = match made {
        Ok(m) => m,
        Err((kind, why)) => return Ok(failed(rt, kind, &why)),
    };
    let forms: Vec<(String, bool)> = seeds.into_iter().map(|t| (t, false)).chain(made).collect();
    let list = strings(rt, forms.iter().map(|(t, k)| (t.as_str(), Some(*k))));
    Ok(sum(rt, "run", list))
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
    let f = rt.heap.product_field(compiler, i);
    let fuel = std::mem::replace(&mut rt.word_fuel, u64::MAX);
    let out = fixpt_runtime::prim::call_front_end(rt, f, args);
    rt.word_fuel = fuel;
    out
}

/// `text`, a session's form, compiled by the session at `base`'s compiler,
/// read in the session's state ([`State::keys`]; the state `made`, while
/// the session is being made), with the reps of a step's types, `rep`, if
/// it is a step's (`ids::with_reps`), given what the checker found of it,
/// and its word run: the value (or,
/// `deferred`, the procedure that runs the forms, `compile-deferred`); or
/// why the compiler would not.
fn compile_run(rt: &mut Runtime, base: usize, made: Option<&mut State>, rep: Option<&[u8]>, text: &str, facts: &FormFacts, deferred: bool) -> Result<Result<Value, String>, String> {
    let (native, registers) = crate::stage::flags(rt).ok_or("this machine cannot keep sessions")?;
    // Read in the session's state (`State::keys`); the session's own, if it
    // is being made and not kept yet (`made`).
    let (at, settings) = match made {
        Some(s) => s.keys(),
        None => with_state(rt, rt.heap.root_at(base), |s| s.keys()).ok_or("a session's code compiled with no state")?,
    };
    // A step's text read with the types it was checked against, its rep and
    // the names it gives types by it (`bind_step_names`).
    let at = match rep {
        Some(r) => crate::ids::with_reps(at, r, &crate::stage::step_reps(r).map(|s| s.named).unwrap_or_default()),
        None => at,
    };
    let compiler = compiler(rt, base)?;
    let mark = rt.heap.push_root(compiler);
    let t = rt.heap.make_string(text);
    rt.heap.push_root(t);
    let f = facts.facts(&mut rt.heap);
    rt.heap.push_root(f);
    let w = facts.withs(&mut rt.heap);
    rt.heap.push_root(w);
    let r = facts.reshapes(&mut rt.heap);
    rt.heap.push_root(r);
    let s = rt.heap.make_string(&settings);
    let [compiler, t, f, w, r] = [0, 1, 2, 3, 4].map(|i| rt.heap.root_at(mark + i));
    rt.heap.pop_roots_to(mark);
    let mode = Value::fixnum(crate::ids::mode() as i64);
    let made = call(rt, compiler, 1, &[mode, Value::fixnum(at), s, t, f, w, r, Value::boolean(native), Value::boolean(registers), Value::boolean(deferred)])?;
    let tag = rt.heap.sum_tag(made);
    let payload = rt.heap.sum_payload(made);
    if tag != rt.heap.intern("made") {
        return Ok(Err(rt.heap.string_to_rust(payload)));
    }
    let run = rt.run_word.ok_or("no cellular machine is installed")?;
    run(rt, payload, &[]).map(Ok)
}
