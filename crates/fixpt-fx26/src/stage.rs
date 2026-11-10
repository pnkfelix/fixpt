//! `stage` as a program runs (`docs/research/eval.md`): what `%fx26-stage`
//! does, installed in the runtime by the session ([`install`]).
//!
//! The form's code is a datum, written out here for the checker to read
//! (so a refusal is placed in what is written). It comes with what the checker that checked the form found
//! the module's type, the effect and the result type to be, printed whole
//! (`n-staged`, which the compilers written in FX-26 put in a product with
//! the text). A front end of its own, made at the first `stage` and kept
//! (`make-stage-check`, the conductor's), checks the text against them in
//! the standard environment alone, and compiles it to a word that makes
//! `(lambda ((m M)) (lambda () (with m text)))`. The word is run on the
//! program's machine and the procedure it makes given the module: the
//! thunk, `(sum ok p)`. A refusal comes back as the front end made it,
//! `(sum failed why)`, `why` a `stage-failure` placed in the text.
//!
//! The checking runs inside the call of `%fx26-stage`, as the front end
//! does for a form: not preempted, not cancellable. That is the design's
//! next step ("Interruptible").

use fixpt_heap::Value;
use fixpt_runtime::Runtime;

const PRODUCT: u8 = fixpt_heap::layout::kind("product");
const SUM: u8 = fixpt_heap::layout::kind("sum");
/// The global holding the front end `stage` checks with, once made.
const CHECK: &str = "fx26-stage:check";
/// The global holding what it is given besides the text: the standard
/// environment as the FX-26 reader read it, and whether the program's
/// convention is native and its words have register code (a product), set
/// by the session ([`settings`]).
const SETTINGS: &str = "fx26-stage:settings";
/// The conductor's entry that makes that front end.
const MAKE_CHECK: &str = "fx26-native:make-stage-check";

/// The session's part: `stage` made possible in `rt`, given the standard
/// environment as the front end read it, and how the program's words are
/// made.
pub fn settings(rt: &mut Runtime, standard: Value, native: bool, registers: bool) {
    let settings = rt.heap.make_frozen(PRODUCT, &[standard, Value::boolean(native), Value::boolean(registers)]);
    set_global(rt, SETTINGS, settings);
    rt.stage = Some(stage);
}

/// The standard environment as the front end read it, as the session set
/// it (`settings`); none where it did not.
pub(crate) fn standard(rt: &mut Runtime) -> Option<Value> {
    let settings = global(rt, SETTINGS)?;
    Some(rt.heap.product_field(settings, 1))
}

/// Whether the program's convention is native and its words have register
/// code, as the session set them (`settings`); none where it did not.
pub(crate) fn flags(rt: &mut Runtime) -> Option<(bool, bool)> {
    let settings = global(rt, SETTINGS)?;
    let field = |i: usize| rt.heap.product_field(settings, i) != Value::FALSE;
    Some((field(2), field(3)))
}

pub(crate) fn global(rt: &mut Runtime, name: &str) -> Option<Value> {
    let sym = rt.heap.intern(name);
    let v = rt.heap.global(rt.heap.symbol_global_slot(sym));
    (!v.is_unbound()).then_some(v)
}

fn set_global(rt: &mut Runtime, name: &str, v: Value) {
    let base = rt.heap.push_root(v);
    let sym = rt.heap.intern(name);
    let v = rt.heap.root_at(base);
    rt.heap.pop_roots_to(base);
    let slot = rt.heap.symbol_global_slot(sym);
    rt.heap.set_global(slot, v);
}

/// A program's code wrapped as every machine checks it: the text, where
/// the code starts in it, in characters (less what of the code is before
/// the part wrapped), and the code's length.
pub(crate) struct Wrapped {
    pub whole: String,
    pub skip: i64,
    pub len: i64,
}

impl Wrapped {
    /// `part` of `code` (at character `at` of it) between `prefix` and
    /// `suffix`.
    pub(crate) fn of(prefix: String, part: &str, suffix: &str, code: &str, at: usize) -> Wrapped {
        let skip = prefix.chars().count() as i64 - at as i64;
        Wrapped { whole: format!("{prefix}{part}{suffix}"), skip, len: code.chars().count() as i64 }
    }

    /// Where byte `b` of the whole is, in characters of the code.
    pub(crate) fn place(&self, b: u32) -> i64 {
        (self.whole[..(b as usize).min(self.whole.len())].chars().count() as i64 - self.skip).clamp(0, self.len)
    }
}

/// `stage`'s: `(the %stage-type (lambda (stage-module) (lambda () (with
/// stage-module code))))`, `%stage-type` the name the rep of what the code
/// is checked as, `(subr pure (M) (subr E () R))`, is imported by
/// (`check-staged-program`): the type not written out, nor read again.
fn stage_wrapped(code: &str) -> Wrapped {
    let prefix = "(the %stage-type\n(lambda (stage-module)\n(lambda () (with stage-module\n".to_string();
    Wrapped::of(prefix, code, "\n))))\n", code, 0)
}

/// What a form's code is checked against: the type it is checked as, as a
/// rep in its binary form (`k-staged-rep`; `docs/research/heap-types.md`,
/// steps 3 and 6), its holes filled by the evidence's reps; none where the
/// checker that noted it made none (a type naming what a rep does not
/// take, an unresolved `select`), which is refused ([`NO_REP`]).
pub(crate) struct Parts {
    pub rep: Option<Vec<u8>>,
}

/// Why code is refused that is checked against a type no rep takes.
pub(crate) const NO_REP: &str = "the code would be checked against a type no rep takes (an unresolved `select`)";

/// The refusal of code checked against a type no rep takes.
pub(crate) fn no_rep(rt: &mut Runtime) -> Value {
    fixpt_runtime::prim::stage_failed(rt, "refused", NO_REP, 0, 0)
}

/// The product the compilers make of a form's code (`n-staged`): a region
/// of its own's mark (a `reify-…`'s, unused here), the code, the names of
/// the variables the type names, of which `given` is the evidence, in
/// order, and the type the code is checked as, as a rep, or `#f`: what the
/// code is checked against, and the code.
pub(crate) fn staged_parts(rt: &Runtime, staged: Value, given: Value) -> Option<(Parts, Value)> {
    let is_product = rt.heap.is_product(staged) && rt.heap.bloblet_len(staged) == 4;
    if !is_product {
        return None;
    }
    let field = |i: usize| rt.heap.product_field(staged, i);
    let given = fixpt_runtime::evidence::Given::of(rt, field(3), given);
    // Its holes, the variables it names, filled by their evidence's reps (a
    // region of its own's too).
    let parts = Parts { rep: given_rep(rt, field(4), &given) };
    Some((parts, field(2)))
}

/// What code given `given` is checked as, by rep (`rep`, a rep in the heap,
/// or `#f`), its holes filled by the evidence's reps: its binary form;
/// none where it has no rep, or a hole is left (the evaluator's sessions,
/// `%fx26-session-eval-check`).
pub(crate) fn given_rep(rt: &Runtime, rep: Value, given: &fixpt_runtime::evidence::Given) -> Option<Vec<u8>> {
    let r = fixpt_reps::heap::from_heap(&rt.heap, rep, true).ok()?;
    let r = if r.holes.is_empty() { Some(r) } else { given.filled(&r) }?;
    Some(fixpt_reps::binary::encode(&r))
}

/// The front end that stages, made at the first `stage` and kept.
fn stage_front_end(rt: &mut Runtime) -> Result<Value, String> {
    if let Some(c) = global(rt, CHECK) {
        return Ok(c);
    }
    let make = global(rt, MAKE_CHECK).ok_or("this machine cannot stage code: its front end is not compiled")?;
    let c = fixpt_runtime::prim::call_front_end(rt, make, &[])?;
    set_global(rt, CHECK, c);
    Ok(global(rt, CHECK).expect("set"))
}

/// `w` checked and compiled by that front end, `rep` the type `w` names
/// `%stage-type` (empty if none): the word that makes the procedure the
/// wrapping is; or the refusal, `(sum failed why)`.
fn compiled(rt: &mut Runtime, w: &Wrapped, rep: &[u8]) -> Result<Result<Value, Value>, String> {
    let settings = global(rt, SETTINGS).ok_or("this machine cannot stage code")?;
    let base = rt.heap.push_root(settings);
    let check = stage_front_end(rt);
    let settings = rt.heap.root_at(base);
    rt.heap.pop_roots_to(base);
    let check = check?;
    let base = rt.heap.push_root(check);
    rt.heap.push_root(settings);
    let whole = rt.heap.make_string(&w.whole);
    rt.heap.push_root(whole);
    let rep = rt.heap.make_bytevector(rep);
    let (check, settings, whole) = (rt.heap.root_at(base), rt.heap.root_at(base + 1), rt.heap.root_at(base + 2));
    rt.heap.pop_roots_to(base);
    let field = |rt: &Runtime, i: usize| rt.heap.product_field(settings, i);
    let args = [field(rt, 1), whole, Value::fixnum(w.skip), Value::fixnum(w.len), field(rt, 2), field(rt, 3), rep, Value::fixnum(crate::ids::mode() as i64)];
    // The front end is licensed code, which ends: no step limit of the
    // program's is its.
    let fuel = std::mem::replace(&mut rt.word_fuel, u64::MAX);
    let checked = fixpt_runtime::prim::call_front_end(rt, check, &args);
    rt.word_fuel = fuel;
    let checked = checked?;
    if rt.heap.sum_tag(checked) != rt.heap.intern("made") {
        return Ok(Err(checked));
    }
    Ok(Ok(rt.heap.sum_payload(checked)))
}

/// `w` compiled, its word run, and the procedure it makes given `args`:
/// what that gives; or the refusal. `args` are rooted from `base`.
fn made(rt: &mut Runtime, w: &Wrapped, rep: &[u8], base: usize, args: usize) -> Result<Result<Value, Value>, String> {
    let word = match compiled(rt, w, rep)? {
        Ok(word) => word,
        Err(refused) => return Ok(Err(refused)),
    };
    let run = rt.run_word.ok_or("no cellular machine is installed")?;
    let mut maker = run(rt, word, &[])?;
    // Compiled as the program's own procedures are, where they are native
    // code (`Runtime::stage_native`), so that it runs as fast and calls
    // between it and the program's code are native calls, in tail position
    // too (Heist's request, `TODO.md` §201); what the compiler declines
    // stays cellular, called through an adapter.
    if let Some(compile) = rt.stage_native {
        let at = rt.heap.push_root(maker);
        let native = compile(rt, maker);
        maker = rt.heap.root_at(at);
        rt.heap.pop_roots_to(at);
        if let Ok(n) = native {
            maker = n;
        }
    }
    let given: Vec<Value> = (0..args).map(|i| rt.heap.root_at(base + i)).collect();
    fixpt_runtime::prim::call_closure(rt, maker, &given).map(Ok)
}

pub(crate) fn ok(rt: &mut Runtime, v: Value) -> Value {
    let base = rt.heap.push_root(v);
    let tag = rt.heap.intern("ok");
    let v = rt.heap.root_at(base);
    rt.heap.pop_roots_to(base);
    rt.heap.make_frozen(SUM, &[tag, v])
}

/// What `%fx26-stage` does with module `m` and `staged`, the product of the
/// module's type, the effect, the result type and the code: the code
/// checked and compiled, the procedure it makes given `m`, the thunk.
fn stage(rt: &mut Runtime, m: Value, staged: Value, given: Value) -> Result<Value, String> {
    let (parts, code) = staged_parts(rt, staged, given).ok_or("this machine cannot stage code")?;
    // The code, a datum, as the checker reads it: written out. A refusal is
    // placed in what is written.
    let text = fixpt_runtime::print::write_value(&rt.heap, code);
    let Some(rep) = parts.rep else { return Ok(no_rep(rt)) };
    let base = rt.heap.push_root(m);
    let out = made(rt, &stage_wrapped(&text), &rep, base, 1);
    rt.heap.pop_roots_to(base);
    match out? {
        Ok(thunk) => Ok(ok(rt, thunk)),
        Err(refused) => Ok(refused),
    }
}

/// `stage` lowered (`rs-scheme-vm`), what `%fx26-stage-lower` does with the
/// product of the module's type, the effect, the result type and the code
/// that the lowering makes (`facts.staged`): the code checked ([`checked`])
/// and lowered: the datum that makes the procedure of the module, in a list
/// of one, which the runtime gives `eval`; or the refusal.
pub fn lower_staged(rt: &mut Runtime, staged: Value, given: Value) -> Result<Value, String> {
    let (parts, code) = staged_parts(rt, staged, given).ok_or("this machine cannot stage code")?;
    let text = fixpt_runtime::print::write_value(&rt.heap, code);
    let Some(rep) = parts.rep else { return Ok(no_rep(rt)) };
    let (c, top) = match checked(rt, &stage_wrapped(&text), &rep) {
        Ok(done) => done,
        Err(refused) => return Ok(refused),
    };
    let code = crate::session::lower_top(&c, &mut crate::lower::Globals::default(), &top);
    let [sx] = &code.0[..] else { return Err("the staged code lowered to more than one form".to_string()) };
    let datum = sx_value(rt, sx);
    Ok(rt.heap.cons(datum, Value::NULL))
}

/// `stage` on the evaluator written in FX-26 (`fx-ast-eval`), what
/// `%fx26-stage-check` does with the code, written out, the names of the
/// variables its type names and their evidence (`given`), and what it is
/// checked as, as a rep (`rep`, the checker's that checked the program, the
/// FX-26 one's, which the Rust one's import takes:
/// `docs/research/heap-types.md`, step 2), its holes filled by the
/// evidence's reps: the code checked ([`checked`]), and the text that was,
/// for the evaluator to parse and run, `(sum checked text)`; or the refusal.
pub fn check_staged(rt: &mut Runtime, text: &str, given: &fixpt_runtime::evidence::Given, rep: Option<fixpt_reps::Rep>) -> Value {
    let rep = rep.and_then(|r| if r.holes.is_empty() { Some(r) } else { given.filled(&r) });
    let Some(rep) = rep.map(|r| fixpt_reps::binary::encode(&r)) else { return no_rep(rt) };
    let w = stage_wrapped(text);
    match checked(rt, &w, &rep) {
        Ok(_) => {
            let tag = rt.heap.intern("checked");
            let whole = rt.heap.make_string(&w.whole);
            rt.heap.make_frozen(SUM, &[tag, whole])
        }
        Err(refused) => refused,
    }
}

/// `w` checked by a checker written in Rust of the standard environment
/// alone, the name `%stage-type` the type of `rep` (a rep's binary form)
/// imported, as the wrapping names it (`stage_wrapped`): the checker and
/// the form; or the refusal, `(sum failed why)`, placed in the code.
pub(crate) fn checked(rt: &mut Runtime, w: &Wrapped, rep: &[u8]) -> Result<(crate::check::Checker, crate::top::Top), Value> {
    let failed = fixpt_runtime::prim::stage_failed;
    let mut c = crate::check::Checker::new();
    let t = fixpt_reps::binary::decode(rep, fixpt_reps::heap::validate_all()).and_then(|r| c.import_rep(&r, &[]));
    match t {
        Ok(t) => {
            let name = c.interner.intern("%stage-type");
            c.dscope.push((name, crate::parse::DScope::Rec(t)));
        }
        Err(why) => return Err(failed(rt, "refused", &format!("a rep: {why}"), 0, w.len)),
    }
    let forms = match c.read_in(fixpt_read::FileId(0), &w.whole) {
        Ok(f) if f.len() == 1 => f,
        Ok(_) => return Err(failed(rt, "unread", "the code is not one whole expression", 0, w.len)),
        Err(e) => return Err(failed(rt, "unread", &e.message, w.place(e.span.start), w.place(e.span.end))),
    };
    match c.top(&forms[0]) {
        Ok(top) => Ok((c, top)),
        Err(e) => Err(failed(rt, "refused", &e.message, w.place(e.span.start), w.place(e.span.end))),
    }
}

/// `x` as a Scheme datum. Allocation does not collect here.
pub(crate) fn sx_value(rt: &mut Runtime, x: &crate::sx::Sx) -> Value {
    use crate::sx::Sx;
    match x {
        Sx::Sym(s) => rt.heap.intern(s),
        Sx::Int(n) => fixpt_runtime::prim::integer_value(rt, *n),
        Sx::Float(f) => rt.heap.make_flonum(*f),
        Sx::Str(s) => rt.heap.make_string(s),
        Sx::Char(c) => Value::char(*c),
        Sx::Bool(b) => Value::boolean(*b),
        Sx::List(items) => {
            let vs: Vec<Value> = items.iter().map(|i| sx_value(rt, i)).collect();
            rt.heap.list_from(&vs)
        }
        Sx::Dotted(items, tail) => {
            let mut out = sx_value(rt, tail);
            for i in items.iter().rev() {
                let v = sx_value(rt, i);
                out = rt.heap.cons(v, out);
            }
            out
        }
        Sx::Vector(items) => {
            let vs: Vec<Value> = items.iter().map(|i| sx_value(rt, i)).collect();
            rt.heap.vector_from(&vs)
        }
        Sx::Keyword(s) => {
            let s = rt.heap.intern(s);
            rt.heap.make_keyword(s)
        }
    }
}

/// What a session's step is checked against, as reps
/// (`docs/research/heap-types.md`, step 6): of the rep of what its code is
/// checked as, `(subr pure (M) (subr E () R))`, `M`'s, `(subr E () R)`'s and
/// `E`'s (an effect, as evidence), each with the name the step's text gives
/// it, in their binary forms; and `M`'s values' names.
#[derive(Clone)]
pub(crate) struct StepReps {
    pub named: Vec<(String, Vec<u8>)>,
    pub values: Vec<String>,
    /// And its types' and effects' names, each with whether it is an
    /// effect, as written in text (`module_descs`).
    pub descs: Vec<(String, bool)>,
}

/// The names a step's text gives its types (`StepReps`).
pub(crate) const MODULE_TYPE: &str = "%stage-module-type";
pub(crate) const RESULT_TYPE: &str = "%stage-result-type";
pub(crate) const EFFECT: &str = "%stage-effect";

/// [`StepReps`] of `bytes`, a rep's binary form; none if it is not of that
/// shape. Kept by the rep, which a session's every step has alike, a few.
pub(crate) fn step_reps(bytes: &[u8]) -> Option<StepReps> {
    thread_local! {
        static KEPT: std::cell::RefCell<Vec<(Vec<u8>, Option<StepReps>)>> = const { std::cell::RefCell::new(Vec::new()) };
    }
    if let Some(r) = KEPT.with(|k| k.borrow().iter().find(|(b, _)| b == bytes).map(|(_, r)| r.clone())) {
        return r;
    }
    let made = step_reps_of(bytes);
    KEPT.with(|k| {
        let mut k = k.borrow_mut();
        if k.len() >= 8 {
            k.remove(0);
        }
        k.push((bytes.to_vec(), made.clone()));
    });
    made
}

fn step_reps_of(bytes: &[u8]) -> Option<StepReps> {
    use fixpt_reps::{fill::part, Arg};
    let rep = fixpt_reps::binary::decode(bytes, fixpt_reps::heap::validate_all()).ok()?;
    let node = |k: u32| rep.nodes.get(k as usize);
    let child = |a: Option<&Arg>| match a {
        Some(Arg::Node(k)) => Some(*k),
        _ => None,
    };
    let root = node(rep.root())?;
    if rep.name(root.head) != "subr" {
        return None;
    }
    let m = child(node(child(root.args.get(2))?)?.args.first())?;
    let result = child(root.args.get(3))?;
    let r = node(result)?;
    if rep.name(r.head) != "subr" {
        return None;
    }
    let e = child(r.args.get(1))?;
    let module = part(&rep, m, false).ok()?;
    let values = module_values(&module)?;
    let descs = module_descs(&module);
    let enc = fixpt_reps::binary::encode;
    let named = vec![
        (MODULE_TYPE.to_string(), enc(&module)),
        (RESULT_TYPE.to_string(), enc(&part(&rep, result, false).ok()?)),
        (EFFECT.to_string(), enc(&part(&rep, e, true).ok()?)),
    ];
    Some(StepReps { named, values, descs })
}

/// The names of module type `module`'s abstract types and descriptions,
/// from its rep (`moduleof`'s binders, and its `descs`, a label then a
/// description each), each with whether it is an effect (a `dlambda` of an
/// effect, `define-effect`'s), as written in text: for a session's steps to
/// name, as staged code does through `with` (Heist's, `TODO.md` §211, 3).
fn module_descs(module: &fixpt_reps::Rep) -> Vec<(String, bool)> {
    let root = &module.nodes[module.root() as usize];
    let mut out: Vec<(String, bool)> = root.binders.iter().map(|b| (fixpt_read::escape_symbol(module.name(*b)), false)).collect();
    let node = |a: &fixpt_reps::Arg| match a {
        fixpt_reps::Arg::Node(k) => Some(&module.nodes[*k as usize]),
        _ => None,
    };
    let Some(descs) = root.args.iter().filter_map(node).find(|n| module.name(n.head) == "descs") else { return out };
    for p in descs.args.chunks(2) {
        let (fixpt_reps::Arg::Sym(s), Some(d)) = (p[0], p.get(1).and_then(node)) else { continue };
        let effect = module.name(d.head) == "dlambda" && d.args.last().and_then(node).is_some_and(|b| module.name(b.head) == "d-effect");
        out.push((fixpt_read::escape_symbol(module.name(s)), effect));
    }
    out
}

/// What defines, in a session's text, each of `descs`' names as the
/// session's module's (`stage-module`'s): as an `import` of them would.
pub(crate) fn desc_defines(descs: &[(String, bool)]) -> String {
    descs
        .iter()
        .map(|(n, effect)| format!("({} {n} (select stage-module {n}))\n", if *effect { "define-effect" } else { "define-type" }))
        .collect()
}

/// The names of module type `module`'s values, from its rep (`moduleof`'s
/// `vals`, a label then a type each), as written in text.
fn module_values(module: &fixpt_reps::Rep) -> Option<Vec<String>> {
    let root = &module.nodes[module.root() as usize];
    if module.name(root.head) != "moduleof" {
        return None;
    }
    let vals = root.args.iter().find_map(|a| match a {
        fixpt_reps::Arg::Node(k) if module.name(module.nodes[*k as usize].head) == "vals" => Some(*k),
        _ => None,
    })?;
    let args = &module.nodes[vals as usize].args;
    Some(args.chunks(2).filter_map(|p| match p[0] {
        fixpt_reps::Arg::Sym(s) => Some(fixpt_read::escape_symbol(module.name(s))),
        _ => None,
    }).collect())
}
