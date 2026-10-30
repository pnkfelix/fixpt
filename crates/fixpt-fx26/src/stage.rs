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

fn global(rt: &mut Runtime, name: &str) -> Option<Value> {
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

/// What `%fx26-stage` does with module `m` and `staged`, the product of the
/// module's type, the effect, the result type and the text.
fn stage(rt: &mut Runtime, m: Value, staged: Value) -> Result<Value, String> {
    let is_product = staged.is_bloblet() && rt.heap.bloblet_kind(staged) == PRODUCT && rt.heap.bloblet_head(staged).fields == 5;
    if !is_product {
        return Err("this machine cannot stage code".to_string());
    }
    let Some(settings) = global(rt, SETTINGS) else { return Err("this machine cannot stage code".to_string()) };
    // Everything held across a call is rooted: any call may collect.
    let base = rt.heap.push_root(m);
    rt.heap.push_root(staged);
    rt.heap.push_root(settings);
    let out = stage_rooted(rt, base);
    rt.heap.pop_roots_to(base);
    out
}

/// [`stage`], its module, its product and the settings roots `base` to
/// `base + 2`.
fn stage_rooted(rt: &mut Runtime, base: usize) -> Result<Value, String> {
    let check = match global(rt, CHECK) {
        Some(c) => c,
        None => {
            let make = global(rt, MAKE_CHECK).ok_or("this machine cannot stage code: its front end is not compiled")?;
            let c = fixpt_runtime::prim::call_front_end(rt, make, &[])?;
            set_global(rt, CHECK, c);
            global(rt, CHECK).expect("set")
        }
    };
    let staged = rt.heap.root_at(base + 1);
    let slot = |rt: &Runtime, v: Value, i: usize| rt.heap.bloblet_slot(v, i + 1);
    // The code, a datum, as the checker reads it: written out. A
    // refusal is placed in what is written.
    let text = fixpt_runtime::print::write_value(&rt.heap, slot(rt, staged, 4));
    let text = rt.heap.make_string(&text);
    let (staged, settings) = (rt.heap.root_at(base + 1), rt.heap.root_at(base + 2));
    let args = [
        slot(rt, settings, 1),
        slot(rt, staged, 1),
        slot(rt, staged, 2),
        slot(rt, staged, 3),
        text,
        slot(rt, settings, 2),
        slot(rt, settings, 3),
    ];
    // The front end is licensed code, which ends: no step limit of the
    // program's is its.
    let fuel = std::mem::replace(&mut rt.word_fuel, u64::MAX);
    let checked = fixpt_runtime::prim::call_front_end(rt, check, &args);
    rt.word_fuel = fuel;
    let checked = checked?;
    let tag = rt.heap.bloblet_slot(checked, 2);
    if tag != rt.heap.intern("made") {
        // `(sum failed why)`, as the form takes it.
        return Ok(checked);
    }
    let word = rt.heap.bloblet_slot(checked, 3);
    let run = rt.run_word.ok_or("no cellular machine is installed")?;
    // The word makes the procedure of the module; given it, the thunk.
    let maker = run(rt, word, &[])?;
    let m = rt.heap.root_at(base);
    let thunk = fixpt_runtime::prim::call_closure(rt, maker, &[m])?;
    let tag = rt.heap.intern("ok");
    Ok(rt.heap.make_frozen(SUM, &[tag, thunk]))
}
