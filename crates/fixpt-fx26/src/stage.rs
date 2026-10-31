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
    Some(rt.heap.bloblet_slot(settings, 2))
}

/// Whether the program's convention is native and its words have register
/// code, as the session set them (`settings`); none where it did not.
pub(crate) fn flags(rt: &mut Runtime) -> Option<(bool, bool)> {
    let settings = global(rt, SETTINGS)?;
    let field = |i: usize| rt.heap.bloblet_slot(settings, i + 1) != Value::FALSE;
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

/// `stage`'s: `(the (subr pure (M) (subr E () R)) (lambda ((stage-module
/// M)) (lambda () (with stage-module code))))`, of `parts`, each region
/// of its own they name bound around it (`bound`).
fn stage_wrapped(parts: &Parts, code: &str) -> Wrapped {
    let Parts { mt, e, r, .. } = parts;
    let prefix = format!("{}(the (subr pure ({mt}) (subr {e} () {r}))\n(lambda ((stage-module {mt}))\n(lambda () (with stage-module\n", parts.bound());
    Wrapped::of(prefix, code, &format!("\n)))){}\n", ")".repeat(parts.closing())), code, 0)
}

/// What a form's code is checked against, as the checker that runs then
/// reads it: the module's type, the effect and the result type, each
/// variable they name given its evidence (`fixpt_runtime::evidence`), and
/// the regions of their own they name.
pub(crate) struct Parts {
    pub mt: String,
    pub e: String,
    pub r: String,
    pub regions: Vec<String>,
}

impl Parts {
    /// Of the texts as printed, given `given`.
    pub(crate) fn of(mt: &str, e: &str, r: &str, given: &fixpt_runtime::evidence::Given) -> Parts {
        let [mt, e, r] = [mt, e, r].map(|t| given.substituted(t));
        let regions = fixpt_runtime::evidence::regions_in(&[&mt, &e, &r]);
        Parts { mt, e, r, regions }
    }

    /// The `plambda` that binds the regions, open; none if none.
    pub(crate) fn bound(&self) -> String {
        if self.regions.is_empty() {
            return String::new();
        }
        let binders: Vec<String> = self.regions.iter().map(|r| format!("({r} region)")).collect();
        format!("(plambda ({})\n", binders.join(" "))
    }

    /// How many parentheses close what `bound` opens.
    pub(crate) fn closing(&self) -> usize {
        usize::from(!self.regions.is_empty())
    }
}

/// The product the compilers make of a form's code (`n-staged`): the
/// module's type, the effect and the result type, the code, and the names
/// of the variables those name, of which `given` is the evidence, in
/// order: what the code is checked against, and the code.
pub(crate) fn staged_parts(rt: &Runtime, staged: Value, given: Value) -> Option<(Parts, Value)> {
    let is_product = staged.is_bloblet() && rt.heap.bloblet_kind(staged) == PRODUCT && rt.heap.bloblet_head(staged).fields == 6;
    if !is_product {
        return None;
    }
    let field = |i: usize| rt.heap.bloblet_slot(staged, i + 1);
    let [mt, e, r] = [1, 2, 3].map(|i| rt.heap.string_to_rust(field(i)));
    let given = fixpt_runtime::evidence::Given::of(rt, field(5), given);
    Some((Parts::of(&mt, &e, &r, &given), field(4)))
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

/// `w` checked and compiled by that front end: the word that makes the
/// procedure the wrapping is; or the refusal, `(sum failed why)`.
fn compiled(rt: &mut Runtime, w: &Wrapped) -> Result<Result<Value, Value>, String> {
    let settings = global(rt, SETTINGS).ok_or("this machine cannot stage code")?;
    let base = rt.heap.push_root(settings);
    let check = stage_front_end(rt);
    let settings = rt.heap.root_at(base);
    rt.heap.pop_roots_to(base);
    let check = check?;
    let base = rt.heap.push_root(check);
    let whole = rt.heap.make_string(&w.whole);
    let check = rt.heap.root_at(base);
    rt.heap.pop_roots_to(base);
    let field = |rt: &Runtime, i: usize| rt.heap.bloblet_slot(settings, i + 1);
    let args = [field(rt, 1), whole, Value::fixnum(w.skip), Value::fixnum(w.len), field(rt, 2), field(rt, 3)];
    // The front end is licensed code, which ends: no step limit of the
    // program's is its.
    let fuel = std::mem::replace(&mut rt.word_fuel, u64::MAX);
    let checked = fixpt_runtime::prim::call_front_end(rt, check, &args);
    rt.word_fuel = fuel;
    let checked = checked?;
    if rt.heap.bloblet_slot(checked, 2) != rt.heap.intern("made") {
        return Ok(Err(checked));
    }
    Ok(Ok(rt.heap.bloblet_slot(checked, 3)))
}

/// `w` compiled, its word run, and the procedure it makes given `args`:
/// what that gives; or the refusal. `args` are rooted from `base`.
fn made(rt: &mut Runtime, w: &Wrapped, base: usize, args: usize) -> Result<Result<Value, Value>, String> {
    let word = match compiled(rt, w)? {
        Ok(word) => word,
        Err(refused) => return Ok(Err(refused)),
    };
    let run = rt.run_word.ok_or("no cellular machine is installed")?;
    let maker = run(rt, word, &[])?;
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
    let base = rt.heap.push_root(m);
    let out = made(rt, &stage_wrapped(&parts, &text), base, 1);
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
    let (c, top) = match checked(rt, &stage_wrapped(&parts, &text)) {
        Ok(done) => done,
        Err(refused) => return Ok(refused),
    };
    let code = crate::session::lower_top(&c, &mut crate::lower::Globals::default(), &top);
    let [sx] = &code.0[..] else { return Err("the staged code lowered to more than one form".to_string()) };
    let datum = sx_value(rt, sx);
    Ok(rt.heap.cons(datum, Value::NULL))
}

/// `stage` on the evaluator written in FX-26 (`fx-ast-eval`), what
/// `%fx26-stage-check` does with the module's type, the effect, the result
/// type and the code, written out, and the names of the variables those
/// name and their evidence (`given`): the code checked ([`checked`]), and
/// the text that was, for the evaluator to parse and run, `(sum checked
/// text)`; or the refusal.
pub fn check_staged(rt: &mut Runtime, mt: &str, e: &str, r: &str, text: &str, given: &fixpt_runtime::evidence::Given) -> Value {
    let w = stage_wrapped(&Parts::of(mt, e, r, given), text);
    match checked(rt, &w) {
        Ok(_) => {
            let tag = rt.heap.intern("checked");
            let whole = rt.heap.make_string(&w.whole);
            rt.heap.make_frozen(SUM, &[tag, whole])
        }
        Err(refused) => refused,
    }
}

/// `w` checked by a checker written in Rust of the standard environment
/// alone: the checker and the form; or the refusal, `(sum failed why)`,
/// placed in the code.
pub(crate) fn checked(rt: &mut Runtime, w: &Wrapped) -> Result<(crate::check::Checker, crate::top::Top), Value> {
    let failed = fixpt_runtime::prim::stage_failed;
    let mut c = crate::check::Checker::new();
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
    }
}
