//! The primitive table.
//!
//! Primitives come in two kinds, and the split is what keeps the engines
//! simple. A [`PrimKind::Simple`] primitive is a leaf: it takes values, returns
//! a value or raises, and cannot re-enter the evaluator. Anything that *must*
//! call back — `apply`, `call/cc`, `dynamic-wind`, `call-with-values` — is a
//! [`PrimKind::Engine`] operation the engine recognises and implements against
//! its own stack.
//!
//! Derived list and control operations that could be primitives (`map`,
//! `for-each`, `assoc`, `member`, `list-copy`, the `caar`…`cddddr` family) are
//! deliberately *not* here. They are written in Scheme in the prelude, where
//! they are shorter, obviously correct, and automatically get proper tail calls
//! and the right behaviour under `call/cc` without any special pleading.

use crate::equal::{eq, equal, eqv};
use crate::error::Outcome;
use crate::num::{N, NumError, RoundMode};
use crate::print::{display_value, write_value};
use crate::runtime::Runtime;
use fixpt_heap::{ObjType, Value};

/// Operations the engine implements itself, because they re-enter evaluation.
///
/// Deliberately few. `dynamic-wind`, `call/cc`'s winding,
/// `with-exception-handler`, `raise`, `raise-continuable` and `force` are all
/// *prelude Scheme* built on top of a raw, winding-unaware `%call/cc` — the
/// classic Dybvig arrangement. Written that way they are a dozen readable lines
/// each, they automatically get proper tail calls, and the engine never has to
/// reason about the interaction between winders and its own frame stack.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum EngineOp {
    Apply,
    /// `(%hole POSITION TOTAL)` — describe the evaluation context and stop.
    ///
    /// Not a computation but a question: *what is going on here?* It needs the
    /// engine because the answer is the engine's own pending work — which
    /// application is collecting arguments, what the earlier ones evaluated to,
    /// what the result would have been used for. A `Simple` primitive sees its
    /// arguments and nothing else.
    Hole,
    /// Raw continuation capture: no `dynamic-wind` awareness at all.
    CallCC,
    Values,
    CallWithValues,

    // ---- continuation marks, prompts and composable continuations ----
    //
    // SRFI 226's control features, in the engine because each one either
    // attaches something to the *current continuation* or cuts it. The winding
    // and handler disciplines built on them stay in the prelude, as before.
    /// `(%wcm key val thunk)` — mark the current continuation, then call
    /// `thunk` in it. `with-continuation-mark` expands to this; the thunk is
    /// called in tail position, so a mark in tail position replaces rather
    /// than accumulates.
    WithMark,
    /// `(%sro kind limit)`: Larceny's SRO, which needs the engine's stacks
    /// as roots.
    Sro,
    /// `(%wind (before . after) thunk)` — enter a `dynamic-wind` extent.
    Wind,
    /// `(%prompt tag handler thunk)` — install a prompt, then call `thunk`.
    Prompt,
    /// `(%current-marks tag)` — this continuation's marks, delimited by `tag`.
    CurrentMarks,
    /// `(%first-mark key default tag)` — the innermost value for `key`.
    FirstMark,
    /// `(%current-winders)` — every live `(before . after)`, innermost first.
    CurrentWinders,
    /// `(%prompt-available? tag)`.
    PromptAvailable,
    /// `(%abort tag vals step)` — cut to the prompt for `tag`, running the
    /// `after` thunk of each extent on the way out through `step`.
    Abort,
    /// `(%call/comp f tag)` — capture the continuation up to the prompt for
    /// `tag`, as a composable continuation, and call `f` with it.
    CallComposable,
    /// `(%throw k vals)` — reinstate a continuation raw, with no winding.
    Throw,
    /// `(%host request …)` — pause the machine and hand `(request …)` to the
    /// native code that called it, which answers by resuming. How a macro
    /// transformer's `rename` and `compare` reach the expander, whose
    /// environment a primitive cannot see.
    Host,
}

pub enum PrimKind {
    Simple(fn(&mut Runtime, &mut [Value]) -> Outcome<Value>),
    Engine(EngineOp),
}

pub struct PrimDef {
    pub name: &'static str,
    pub min: usize,
    /// `None` means variadic.
    pub max: Option<usize>,
    pub kind: PrimKind,
}

impl PrimDef {
    pub fn accepts(&self, n: usize) -> bool {
        n >= self.min && self.max.is_none_or(|m| n <= m)
    }
}

// ---------------------------------------------------------------- helpers

fn num(rt: &mut Runtime, v: Value) -> Outcome<N> {
    match N::load(&rt.heap, v) {
        Some(n) => Ok(n),
        None => rt.type_error("a number", v),
    }
}

fn int(rt: &mut Runtime, v: Value) -> Outcome<i64> {
    if v.is_fixnum() {
        return Ok(v.as_fixnum());
    }
    rt.type_error("an exact integer that fits a machine word", v)
}

/// `op` on two fixnums, a fixnum or "integer overflow".
fn fx26_arith(rt: &mut Runtime, a: &[Value], op: fn(i64, i64) -> Option<i64>) -> Outcome<Value> {
    let (x, y) = (int(rt, a[0])?, int(rt, a[1])?);
    match op(x, y).and_then(Value::try_fixnum) {
        Some(v) => Ok(v),
        None => rt.fail("integer overflow", &[a[0], a[1]]),
    }
}

/// `%run-word`'s work, by the machine `run`.
fn run_word_by(rt: &mut Runtime, a: &[Value], run: Option<crate::RunWord>) -> Outcome<Value> {
    let Some(args) = rt.heap.list_to_vec(a[1]) else { return rt.type_error("a list of arguments", a[1]) };
    // A closure is called by a word of its own, run with no arguments:
    // `lit a1 … lit an lit closure call n exit`. A word's frame starts
    // above what it is run on, so the arguments are the word's to push.
    // Allocation does not collect here.
    let (word, args) = if a[0].is_bloblet() && rt.heap.bloblet_kind(a[0]) == fixpt_heap::layout::kind("cellular-closure") {
        use fixpt_heap::layout::cellular::routine;
        let f = |n: u64| Value::fixnum(n as i64);
        let mut cells = Vec::with_capacity(2 * args.len() + 5);
        for x in &args {
            cells.extend([f(routine("lit")), *x]);
        }
        cells.extend([f(routine("lit")), a[0], f(routine("call")), f(args.len() as u64), f(routine("exit"))]);
        let name = rt.heap.intern("call-closure");
        match rt.heap.make_cellular_word(name, &cells) {
            Ok(w) => (w, Vec::new()),
            Err(e) => return rt.fail(&e, &[a[0]]),
        }
    } else if rt.heap.is_cellular_word(a[0]) {
        (a[0], args)
    } else {
        return rt.type_error("a cellular word or closure", a[0]);
    };
    let Some(run) = run else { return rt.fail("no cellular machine is installed", &[]) };
    // With `FIXPT_TIME_WORDS` set, how long each run took: the machine
    // alone, without the front end around it.
    let started = std::env::var_os("FIXPT_TIME_WORDS").map(|_| std::time::Instant::now());
    let out = run(rt, word, &args);
    if let Some(t) = started {
        eprintln!("run-word: {:.6} s", t.elapsed().as_secs_f64());
    }
    match out {
        Ok(v) => Ok(v),
        Err(e) => rt.fail(&format!("cellular word: {e}"), &[a[0]]),
    }
}

/// A fixed-width integer type: its bits, and whether it is signed.
#[derive(Clone, Copy)]
enum Width {
    I32,
    U32,
    I64,
    U64,
}

impl Width {
    fn bits(self) -> u32 {
        match self {
            Width::I32 | Width::U32 => 32,
            Width::I64 | Width::U64 => 64,
        }
    }
    fn signed(self) -> bool {
        matches!(self, Width::I32 | Width::I64)
    }
    fn name(self) -> &'static str {
        match self {
            Width::I32 => "an i32",
            Width::U32 => "a u32",
            Width::I64 => "an i64",
            Width::U64 => "a u64",
        }
    }
    /// `x` wrapped to this width: its low bits, sign-extended if signed.
    fn wrap(self, x: i128) -> i128 {
        let b = self.bits();
        let low = x & ((1i128 << b) - 1);
        if self.signed() && low >> (b - 1) == 1 { low - (1i128 << b) } else { low }
    }
}

/// An exact integer, as an `i128`, if it is one that fits.
fn exact_i128(rt: &Runtime, v: Value) -> Option<i128> {
    if v.is_fixnum() {
        return Some(v.as_fixnum() as i128);
    }
    crate::num::N::load(&rt.heap, v).filter(|n| matches!(n, crate::num::N::Big(_))).and_then(|n| n.to_bigint()).and_then(|b| i128::try_from(b).ok())
}

/// A value of width `w`: the integer it stands for.
fn fixed_in(rt: &mut Runtime, v: Value, w: Width) -> Outcome<i128> {
    match exact_i128(rt, v) {
        Some(x) if w.wrap(x) == x => Ok(x),
        _ => rt.type_error(w.name(), v),
    }
}

/// The integer `x`, as the runtime keeps it: a fixnum where it fits.
fn exact_out(rt: &mut Runtime, x: i128) -> Value {
    crate::num::N::big(num_bigint::BigInt::from(x)).store(&mut rt.heap)
}

/// The integer `x` as the runtime keeps it: a fixnum where it fits, else a
/// bignum. For native code's `i64` and `u64`, boxed.
pub fn integer_value(rt: &mut Runtime, x: i128) -> Value {
    exact_out(rt, x)
}

/// An exact integer's low 64 bits, two's complement: an `i64` or `u64`
/// raw, or `int->u64` wrapping. 0 for what is no exact integer.
pub fn low_64_bits(rt: &Runtime, v: Value) -> u64 {
    match exact_bigint(rt, v) {
        Some(b) => {
            let m = num_bigint::BigInt::from(1u8) << 64;
            let low = ((b % &m) + &m) % &m;
            u64::try_from(low).expect("under 2^64")
        }
        None => 0,
    }
}

/// Whether primitive `name` never collects, and so may be called from
/// code whose live values are in registers, not in a frame (register code's
/// `prim1`, `prim2`, `prim2imm`): FX-26's `*`, `quotient` and `modulo`, and
/// the fixed-width integers' operations. It may allocate (an `i64` past a
/// fixnum is a bignum), since allocation never collects: a collection waits
/// for the next point that may. It may fail, which ends the run.
pub fn never_collects(name: &str) -> bool {
    matches!(name, "%fx26-mul" | "%fx26-quotient" | "modulo")
        || ["%fx26-i32", "%fx26-u32", "%fx26-i64", "%fx26-u64", "%fx26-int->"].iter().any(|p| name.starts_with(p))
}

/// Operation `op` of the fixed-width integers of width `w`.
fn fixed_op(rt: &mut Runtime, a: &[Value], op: &str, w: Width) -> Outcome<Value> {
    match op {
        // `int->T`: any exact integer, wrapped.
        "from" => {
            let x = match exact_bigint(rt, a[0]) {
                Some(b) => b,
                None => return rt.type_error("an exact integer", a[0]),
            };
            let m = num_bigint::BigInt::from(1u8) << w.bits();
            let low = ((x % &m) + &m) % &m;
            let low = i128::try_from(low).expect("under 2^64");
            return Ok(exact_out(rt, w.wrap(low)));
        }
        // `T->int`: an `int` is a fixnum until it may be a bignum (PLAN.md,
        // Q2), so past one it fails, as `+` does.
        "to" => {
            let x = fixed_in(rt, a[0], w)?;
            return match i64::try_from(x).ok().and_then(Value::try_fixnum) {
                Some(v) => Ok(v),
                None => rt.fail("integer overflow", &[a[0]]),
            };
        }
        _ => {}
    }
    let x = fixed_in(rt, a[0], w)?;
    if op == "not" {
        return Ok(exact_out(rt, w.wrap(!x)));
    }
    if op == "shl" || op == "shr" {
        let k = (int(rt, a[1])? as u32) & (w.bits() - 1);
        // Signed: arithmetic; unsigned: logical (`x` is non-negative).
        let r = if op == "shl" { x << k } else { x >> k };
        return Ok(exact_out(rt, w.wrap(r)));
    }
    let y = fixed_in(rt, a[1], w)?;
    let r = match op {
        "add" => x + y,
        "sub" => x - y,
        "mul" => x.wrapping_mul(y),
        "quot" | "rem" => {
            if y == 0 {
                return rt.fail("division by zero", &[a[0], a[1]]);
            }
            if op == "quot" { x / y } else { x % y }
        }
        "and" => x & y,
        "or" => x | y,
        "xor" => x ^ y,
        "lt" => return Ok(Value::boolean(x < y)),
        "le" => return Ok(Value::boolean(x <= y)),
        "gt" => return Ok(Value::boolean(x > y)),
        "ge" => return Ok(Value::boolean(x >= y)),
        "eq" => return Ok(Value::boolean(x == y)),
        _ => unreachable!("a fixed-width operation"),
    };
    Ok(exact_out(rt, w.wrap(r)))
}

/// Any exact integer, as a big integer.
fn exact_bigint(rt: &Runtime, v: Value) -> Option<num_bigint::BigInt> {
    if v.is_fixnum() {
        return Some(num_bigint::BigInt::from(v.as_fixnum()));
    }
    crate::num::N::load(&rt.heap, v).filter(|n| matches!(n, crate::num::N::Big(_))).and_then(|n| n.to_bigint())
}

/// A radix, 2 to 36.
fn radix(rt: &mut Runtime, v: Value) -> Outcome<u32> {
    match int(rt, v)? {
        r @ 2..=36 => Ok(r as u32),
        _ => rt.fail("a radix is from 2 to 36", &[v]),
    }
}

/// `%sro`'s work, given the engine's stacks as extra roots.
pub fn sro(rt: &mut Runtime, kind: Value, limit: Value, extra: &[&[Value]]) -> Outcome<Value> {
    let kind = if kind.is_false() {
        fixpt_heap::SroKind::Any
    } else if rt.heap.is_a(kind, ObjType::Symbol) {
        let name = rt.heap.symbol_name(kind);
        if name == "pair" {
            fixpt_heap::SroKind::Pair
        } else {
            match fixpt_heap::layout::KINDS.iter().find(|k| k.name == name) {
                Some(k) => fixpt_heap::SroKind::Kind(k.code),
                None => return rt.fail("%sro: no such kind", &[kind]),
            }
        }
    } else {
        return rt.type_error("a kind's name, `pair`, or #f", kind);
    };
    let limit = if limit.is_false() { None } else { Some(int(rt, limit)?.max(1) as usize) };
    let found = rt.heap.sro(kind, limit, extra);
    Ok(rt.heap.vector_from(&found))
}

/// The kind of a bloblet made by `%make-bloblet`.
const PLAIN_BLOBLET: u8 = fixpt_heap::layout::kind("bloblet");
const SUM_KIND: u8 = fixpt_heap::layout::kind("sum");
const PRODUCT_KIND: u8 = fixpt_heap::layout::kind("product");

fn bloblet(rt: &mut Runtime, v: Value) -> Outcome<Value> {
    if v.is_bloblet() { Ok(v) } else { rt.type_error("a bloblet", v) }
}

/// A bloblet of kind `bloblet`: one the program made, so one it may change.
fn plain_bloblet(rt: &mut Runtime, v: Value) -> Outcome<Value> {
    if v.is_bloblet() && rt.heap.bloblet_kind(v) == PLAIN_BLOBLET {
        Ok(v)
    } else {
        rt.type_error("a bloblet the program made", v)
    }
}

fn index(rt: &mut Runtime, v: Value, len: usize, what: &str) -> Outcome<usize> {
    let i = int(rt, v)?;
    if i < 0 || i as usize >= len {
        return rt.fail(&format!("{what} index out of range (length {len})"), &[v]);
    }
    Ok(i as usize)
}

fn numeric_error<T>(rt: &mut Runtime, e: NumError, irritants: &[Value]) -> Outcome<T> {
    rt.fail(&e.to_string(), irritants)
}

fn fold_num(
    rt: &mut Runtime,
    args: &mut [Value],
    init: N,
    f: impl Fn(&N, &N) -> N,
) -> Outcome<Value> {
    let mut acc = init;
    for v in args.iter().copied() {
        let n = num(rt, v)?;
        acc = f(&acc, &n);
    }
    Ok(acc.store(&mut rt.heap))
}

fn compare_chain(
    rt: &mut Runtime,
    args: &mut [Value],
    ok: impl Fn(std::cmp::Ordering) -> bool,
) -> Outcome<Value> {
    for i in 0..args.len().saturating_sub(1) {
        let a = num(rt, args[i])?;
        let b = num(rt, args[i + 1])?;
        match a.cmp_num(&b) {
            Some(o) if ok(o) => {}
            // NaN compares false against everything, including itself.
            _ => return Ok(Value::FALSE),
        }
    }
    Ok(Value::TRUE)
}

fn get_string(rt: &mut Runtime, v: Value) -> Outcome<String> {
    if rt.heap.is_a(v, ObjType::String) {
        return Ok(rt.heap.string_to_rust(v));
    }
    rt.type_error("a string", v)
}

fn get_char(rt: &mut Runtime, v: Value) -> Outcome<char> {
    if v.is_char() {
        return Ok(v.as_char());
    }
    rt.type_error("a character", v)
}

/// A procedure is a closure, a primitive object, or a continuation.
pub fn is_procedure(rt: &Runtime, v: Value) -> bool {
    matches!(
        rt.heap.obj_type(v),
        Some(ObjType::Closure) | Some(ObjType::Primitive) | Some(ObjType::Continuation)
    )
}

// ------------------------------------------------------------------ table

macro_rules! prims {
    ($($name:literal, $min:literal, $max:expr, $kind:expr;)*) => {
        pub static PRIMITIVES: &[PrimDef] = &[
            $(PrimDef { name: $name, min: $min, max: $max, kind: $kind }),*
        ];
    };
}

macro_rules! simple {
    (|$rt:ident, $a:ident| $body:expr) => {
        PrimKind::Simple(|$rt: &mut Runtime, $a: &mut [Value]| -> Outcome<Value> { $body })
    };
}

prims! {
    // ---- equivalence ----
    "eq?",     2, Some(2), simple!(|rt, a| { let _ = &rt; Ok(Value::boolean(eq(a[0], a[1]))) });
    "eqv?",    2, Some(2), simple!(|rt, a| Ok(Value::boolean(eqv(&rt.heap, a[0], a[1]))));
    "equal?",  2, Some(2), simple!(|rt, a| Ok(Value::boolean(equal(&rt.heap, a[0], a[1]))));
    "not",     1, Some(1), simple!(|rt, a| { let _ = &rt; Ok(Value::boolean(a[0].is_false())) });

    // ---- type predicates ----
    "pair?",      1, Some(1), simple!(|rt, a| { let _ = &rt; Ok(Value::boolean(a[0].is_pair())) });
    "null?",      1, Some(1), simple!(|rt, a| { let _ = &rt; Ok(Value::boolean(a[0].is_null())) });
    "boolean?",   1, Some(1), simple!(|rt, a| { let _ = &rt; Ok(Value::boolean(a[0].is_boolean())) });
    "symbol?",    1, Some(1), simple!(|rt, a| Ok(Value::boolean(rt.heap.is_a(a[0], ObjType::Symbol))));
    "string?",    1, Some(1), simple!(|rt, a| Ok(Value::boolean(rt.heap.is_a(a[0], ObjType::String))));
    "char?",      1, Some(1), simple!(|rt, a| { let _ = &rt; Ok(Value::boolean(a[0].is_char())) });
    "vector?",    1, Some(1), simple!(|rt, a| Ok(Value::boolean(rt.heap.is_a(a[0], ObjType::Vector))));
    "bytevector?",1, Some(1), simple!(|rt, a| Ok(Value::boolean(rt.heap.is_a(a[0], ObjType::Bytevector))));
    "procedure?", 1, Some(1), simple!(|rt, a| Ok(Value::boolean(is_procedure(rt, a[0]))));
    "number?",    1, Some(1), simple!(|rt, a| Ok(Value::boolean(N::load(&rt.heap, a[0]).is_some())));
    "eof-object?",1, Some(1), simple!(|rt, a| { let _ = &rt; Ok(Value::boolean(a[0].is_eof())) });
    "eof-object", 0, Some(0), simple!(|rt, a| { let _ = (&rt, &a); Ok(Value::EOF) });

    "integer?", 1, Some(1), simple!(|rt, a|
        Ok(Value::boolean(N::load(&rt.heap, a[0]).is_some_and(|n| n.is_integer()))));
    "rational?", 1, Some(1), simple!(|rt, a|
        Ok(Value::boolean(N::load(&rt.heap, a[0]).is_some_and(|n| n.is_exact() || n.to_f64().is_finite()))));
    "real?", 1, Some(1), simple!(|rt, a| Ok(Value::boolean(N::load(&rt.heap, a[0]).is_some())));
    "exact?", 1, Some(1), simple!(|rt, a| { let n = num(rt, a[0])?; Ok(Value::boolean(n.is_exact())) });
    "inexact?", 1, Some(1), simple!(|rt, a| { let n = num(rt, a[0])?; Ok(Value::boolean(!n.is_exact())) });
    "exact-integer?", 1, Some(1), simple!(|rt, a|
        Ok(Value::boolean(N::load(&rt.heap, a[0]).is_some_and(|n| n.is_exact() && n.is_integer()))));
    "nan?", 1, Some(1), simple!(|rt, a| { let n = num(rt, a[0])?; Ok(Value::boolean(n.to_f64().is_nan())) });

    // ---- arithmetic ----
    "+", 0, None, simple!(|rt, a| fold_num(rt, a, N::Fix(0), |x, y| x.add(y)));
    "*", 0, None, simple!(|rt, a| fold_num(rt, a, N::Fix(1), |x, y| x.mul(y)));
    "-", 1, None, simple!(|rt, a| {
        let first = num(rt, a[0])?;
        if a.len() == 1 { return Ok(first.neg().store(&mut rt.heap)); }
        fold_num(rt, &mut a[1..], first, |x, y| x.sub(y))
    });
    "/", 1, None, simple!(|rt, a| {
        let first = num(rt, a[0])?;
        let mut acc = if a.len() == 1 {
            match N::Fix(1).div(&first) { Ok(v) => v, Err(e) => return numeric_error(rt, e, &[a[0]]) }
        } else { first };
        for (i, v) in a.iter().copied().enumerate().skip(1) {
            let n = num(rt, v)?;
            acc = match acc.div(&n) { Ok(v) => v, Err(e) => return numeric_error(rt, e, &[a[i]]) };
        }
        Ok(acc.store(&mut rt.heap))
    });
    "=",  1, None, simple!(|rt, a| compare_chain(rt, a, |o| o == std::cmp::Ordering::Equal));
    "<",  1, None, simple!(|rt, a| compare_chain(rt, a, |o| o == std::cmp::Ordering::Less));
    ">",  1, None, simple!(|rt, a| compare_chain(rt, a, |o| o == std::cmp::Ordering::Greater));
    "<=", 1, None, simple!(|rt, a| compare_chain(rt, a, |o| o != std::cmp::Ordering::Greater));
    ">=", 1, None, simple!(|rt, a| compare_chain(rt, a, |o| o != std::cmp::Ordering::Less));

    "quotient",  2, Some(2), simple!(|rt, a| {
        let (x, y) = (num(rt, a[0])?, num(rt, a[1])?);
        match x.quotient(&y) { Ok(v) => Ok(v.store(&mut rt.heap)), Err(e) => numeric_error(rt, e, &[a[0], a[1]]) }
    });
    "remainder", 2, Some(2), simple!(|rt, a| {
        let (x, y) = (num(rt, a[0])?, num(rt, a[1])?);
        match x.remainder(&y) { Ok(v) => Ok(v.store(&mut rt.heap)), Err(e) => numeric_error(rt, e, &[a[0], a[1]]) }
    });
    "modulo",    2, Some(2), simple!(|rt, a| {
        let (x, y) = (num(rt, a[0])?, num(rt, a[1])?);
        match x.modulo(&y) { Ok(v) => Ok(v.store(&mut rt.heap)), Err(e) => numeric_error(rt, e, &[a[0], a[1]]) }
    });
    "abs", 1, Some(1), simple!(|rt, a| { let n = num(rt, a[0])?; Ok(n.abs().store(&mut rt.heap)) });
    "gcd", 0, None, simple!(|rt, a| {
        let mut acc = N::Fix(0);
        for (i, v) in a.iter().copied().enumerate() {
            let n = num(rt, v)?;
            acc = match acc.gcd(&n) { Ok(v) => v, Err(e) => return numeric_error(rt, e, &[a[i]]) };
        }
        Ok(acc.abs().store(&mut rt.heap))
    });
    "expt", 2, Some(2), simple!(|rt, a| {
        let (x, y) = (num(rt, a[0])?, num(rt, a[1])?);
        match x.expt(&y) { Ok(v) => Ok(v.store(&mut rt.heap)), Err(e) => numeric_error(rt, e, &[a[0], a[1]]) }
    });
    "%numerator", 1, Some(1), simple!(|rt, a| {
        let n = num(rt, a[0])?;
        Ok(n.numerator().store(&mut rt.heap))
    });
    "%denominator", 1, Some(1), simple!(|rt, a| {
        let n = num(rt, a[0])?;
        Ok(n.denominator().store(&mut rt.heap))
    });
    "sqrt", 1, Some(1), simple!(|rt, a| { let n = num(rt, a[0])?; Ok(n.sqrt().store(&mut rt.heap)) });
    "floor",    1, Some(1), simple!(|rt, a| { let n = num(rt, a[0])?; Ok(n.round_with(RoundMode::Floor).store(&mut rt.heap)) });
    "ceiling",  1, Some(1), simple!(|rt, a| { let n = num(rt, a[0])?; Ok(n.round_with(RoundMode::Ceiling).store(&mut rt.heap)) });
    "truncate", 1, Some(1), simple!(|rt, a| { let n = num(rt, a[0])?; Ok(n.round_with(RoundMode::Truncate).store(&mut rt.heap)) });
    "round",    1, Some(1), simple!(|rt, a| { let n = num(rt, a[0])?; Ok(n.round_with(RoundMode::Round).store(&mut rt.heap)) });
    "exact",    1, Some(1), simple!(|rt, a| {
        let n = num(rt, a[0])?;
        match n.exact() { Ok(v) => Ok(v.store(&mut rt.heap)), Err(e) => numeric_error(rt, e, &[a[0]]) }
    });
    "inexact",  1, Some(1), simple!(|rt, a| { let n = num(rt, a[0])?; Ok(n.inexact().store(&mut rt.heap)) });
    "number->string", 1, Some(2), simple!(|rt, a| {
        let n = num(rt, a[0])?;
        let radix = if a.len() > 1 { int(rt, a[1])? as u32 } else { 10 };
        let s = n.to_string_radix(radix);
        Ok(rt.heap.make_string(&s))
    });
    "string->number", 1, Some(2), simple!(|rt, a| {
        let s = get_string(rt, a[0])?;
        let radix = if a.len() > 1 { int(rt, a[1])? as u32 } else { 10 };
        match fixpt_read::reader::parse_number(&s, radix, None) {
            Some(n) => Ok(crate::num_from_literal(rt, &n)),
            None => Ok(Value::FALSE),
        }
    });

    // ---- pairs and lists ----
    "cons", 2, Some(2), simple!(|rt, a| Ok(rt.heap.cons(a[0], a[1])));
    "car",  1, Some(1), simple!(|rt, a| {
        if a[0].is_pair() { Ok(rt.heap.car(a[0])) } else { rt.type_error("a pair", a[0]) }
    });
    "cdr",  1, Some(1), simple!(|rt, a| {
        if a[0].is_pair() { Ok(rt.heap.cdr(a[0])) } else { rt.type_error("a pair", a[0]) }
    });
    "set-car!", 2, Some(2), simple!(|rt, a| {
        if !a[0].is_pair() { return rt.type_error("a pair", a[0]); }
        rt.heap.set_car(a[0], a[1]); Ok(Value::UNSPECIFIED)
    });
    "set-cdr!", 2, Some(2), simple!(|rt, a| {
        if !a[0].is_pair() { return rt.type_error("a pair", a[0]); }
        rt.heap.set_cdr(a[0], a[1]); Ok(Value::UNSPECIFIED)
    });
    "list", 0, None, simple!(|rt, a| Ok(rt.heap.list_from(a)));
    "length", 1, Some(1), simple!(|rt, a| {
        match rt.heap.list_to_vec(a[0]) {
            Some(v) => Ok(Value::fixnum(v.len() as i64)),
            None => rt.type_error("a proper list", a[0]),
        }
    });
    "append", 0, None, simple!(|rt, a| {
        if a.is_empty() { return Ok(Value::NULL); }
        let last = a[a.len() - 1];
        let mut front: Vec<Value> = Vec::new();
        for v in a[..a.len() - 1].iter().copied() {
            match rt.heap.list_to_vec(v) {
                Some(mut items) => front.append(&mut items),
                None => return rt.type_error("a proper list", v),
            }
        }
        let mut acc = last;
        for v in front.into_iter().rev() { acc = rt.heap.cons(v, acc); }
        Ok(acc)
    });
    "reverse", 1, Some(1), simple!(|rt, a| {
        match rt.heap.list_to_vec(a[0]) {
            Some(v) => { let mut acc = Value::NULL; for x in v { acc = rt.heap.cons(x, acc); } Ok(acc) }
            None => rt.type_error("a proper list", a[0]),
        }
    });

    // ---- symbols ----
    "symbol->string", 1, Some(1), simple!(|rt, a| {
        if !rt.heap.is_a(a[0], ObjType::Symbol) { return rt.type_error("a symbol", a[0]); }
        let s = rt.heap.symbol_name(a[0]);
        Ok(rt.heap.make_string(&s))
    });
    "string->symbol", 1, Some(1), simple!(|rt, a| {
        let s = get_string(rt, a[0])?;
        Ok(rt.heap.intern(&s))
    });

    // ---- characters ----
    "char->integer", 1, Some(1), simple!(|rt, a| { let c = get_char(rt, a[0])?; Ok(Value::fixnum(c as i64)) });
    "integer->char", 1, Some(1), simple!(|rt, a| {
        let n = int(rt, a[0])?;
        match u32::try_from(n).ok().and_then(char::from_u32) {
            Some(c) => Ok(Value::char(c)),
            None => rt.fail("not a Unicode scalar value", &[a[0]]),
        }
    });
    "char-upcase",   1, Some(1), simple!(|rt, a| { let c = get_char(rt, a[0])?; Ok(Value::char(c.to_uppercase().next().unwrap_or(c))) });
    "char-downcase", 1, Some(1), simple!(|rt, a| { let c = get_char(rt, a[0])?; Ok(Value::char(c.to_lowercase().next().unwrap_or(c))) });
    "char-alphabetic?", 1, Some(1), simple!(|rt, a| { let c = get_char(rt, a[0])?; Ok(Value::boolean(c.is_alphabetic())) });
    "char-numeric?",    1, Some(1), simple!(|rt, a| { let c = get_char(rt, a[0])?; Ok(Value::boolean(c.is_numeric())) });
    "char-whitespace?", 1, Some(1), simple!(|rt, a| { let c = get_char(rt, a[0])?; Ok(Value::boolean(c.is_whitespace())) });
    "char-upper-case?", 1, Some(1), simple!(|rt, a| { let c = get_char(rt, a[0])?; Ok(Value::boolean(c.is_uppercase())) });
    "char-lower-case?", 1, Some(1), simple!(|rt, a| { let c = get_char(rt, a[0])?; Ok(Value::boolean(c.is_lowercase())) });

    // ---- strings ----
    "string-length", 1, Some(1), simple!(|rt, a| {
        if !rt.heap.is_a(a[0], ObjType::String) { return rt.type_error("a string", a[0]); }
        Ok(Value::fixnum(rt.heap.string_len(a[0]) as i64))
    });
    "string-ref", 2, Some(2), simple!(|rt, a| {
        if !rt.heap.is_a(a[0], ObjType::String) { return rt.type_error("a string", a[0]); }
        let n = rt.heap.string_len(a[0]);
        let i = index(rt, a[1], n, "string")?;
        Ok(Value::char(rt.heap.string_ref(a[0], i)))
    });
    "string-set!", 3, Some(3), simple!(|rt, a| {
        if !rt.heap.is_a(a[0], ObjType::String) { return rt.type_error("a string", a[0]); }
        let n = rt.heap.string_len(a[0]);
        let i = index(rt, a[1], n, "string")?;
        let c = get_char(rt, a[2])?;
        rt.heap.string_set(a[0], i, c);
        Ok(Value::UNSPECIFIED)
    });
    "make-string", 1, Some(2), simple!(|rt, a| {
        let n = int(rt, a[0])?;
        if n < 0 { return rt.fail("string length must be non-negative", &[a[0]]); }
        let c = if a.len() > 1 { get_char(rt, a[1])? } else { ' ' };
        let chars = vec![c; n as usize];
        Ok(rt.heap.string_from_chars(&chars))
    });
    "string", 0, None, simple!(|rt, a| {
        let mut chars = Vec::with_capacity(a.len());
        for v in a.iter().copied() { chars.push(get_char(rt, v)?); }
        Ok(rt.heap.string_from_chars(&chars))
    });
    // In time for the part taken, not the whole string: a reader takes
    // each atom of a file's text so.
    "substring", 3, Some(3), simple!(|rt, a| {
        if !rt.heap.is_a(a[0], ObjType::String) { return rt.type_error("a string", a[0]); }
        let n = rt.heap.string_len(a[0]);
        let start = int(rt, a[1])?; let end = int(rt, a[2])?;
        if start < 0 || end < start || end as usize > n {
            return rt.fail("substring range out of bounds", &[a[1], a[2]]);
        }
        let chars: Vec<char> = (start as usize..end as usize).map(|i| rt.heap.string_ref(a[0], i)).collect();
        Ok(rt.heap.string_from_chars(&chars))
    });
    "string-append", 0, None, simple!(|rt, a| {
        let mut out = String::new();
        for v in a.iter().copied() { out.push_str(&get_string(rt, v)?); }
        Ok(rt.heap.make_string(&out))
    });
    "string->list", 1, Some(1), simple!(|rt, a| {
        let s = get_string(rt, a[0])?;
        let items: Vec<Value> = s.chars().map(Value::char).collect();
        Ok(rt.heap.list_from(&items))
    });
    "list->string", 1, Some(1), simple!(|rt, a| {
        let items = match rt.heap.list_to_vec(a[0]) { Some(v) => v, None => return rt.type_error("a proper list", a[0]) };
        let mut chars = Vec::with_capacity(items.len());
        for v in items { chars.push(get_char(rt, v)?); }
        Ok(rt.heap.string_from_chars(&chars))
    });
    "string=?", 1, None, simple!(|rt, a| string_chain(rt, a, |o| o == std::cmp::Ordering::Equal));
    "string<?", 1, None, simple!(|rt, a| string_chain(rt, a, |o| o == std::cmp::Ordering::Less));
    "string>?", 1, None, simple!(|rt, a| string_chain(rt, a, |o| o == std::cmp::Ordering::Greater));
    "string<=?",1, None, simple!(|rt, a| string_chain(rt, a, |o| o != std::cmp::Ordering::Greater));
    "string>=?",1, None, simple!(|rt, a| string_chain(rt, a, |o| o != std::cmp::Ordering::Less));

    // ---- vectors ----
    "make-vector", 1, Some(2), simple!(|rt, a| {
        let n = int(rt, a[0])?;
        if n < 0 { return rt.fail("vector length must be non-negative", &[a[0]]); }
        let fill = if a.len() > 1 { a[1] } else { Value::UNSPECIFIED };
        Ok(rt.heap.make_vector(n as usize, fill))
    });
    "vector", 0, None, simple!(|rt, a| Ok(rt.heap.vector_from(a)));
    "vector-length", 1, Some(1), simple!(|rt, a| {
        if !rt.heap.is_a(a[0], ObjType::Vector) { return rt.type_error("a vector", a[0]); }
        Ok(Value::fixnum(rt.heap.obj_len(a[0]) as i64))
    });
    "vector-ref", 2, Some(2), simple!(|rt, a| {
        if !rt.heap.is_a(a[0], ObjType::Vector) { return rt.type_error("a vector", a[0]); }
        let n = rt.heap.obj_len(a[0]);
        let i = index(rt, a[1], n, "vector")?;
        Ok(rt.heap.obj_ref(a[0], i))
    });
    "vector-set!", 3, Some(3), simple!(|rt, a| {
        if !rt.heap.is_a(a[0], ObjType::Vector) { return rt.type_error("a vector", a[0]); }
        let n = rt.heap.obj_len(a[0]);
        let i = index(rt, a[1], n, "vector")?;
        rt.heap.obj_set(a[0], i, a[2]);
        Ok(Value::UNSPECIFIED)
    });
    "vector->list", 1, Some(1), simple!(|rt, a| {
        if !rt.heap.is_a(a[0], ObjType::Vector) { return rt.type_error("a vector", a[0]); }
        let items: Vec<Value> = (0..rt.heap.obj_len(a[0])).map(|i| rt.heap.obj_ref(a[0], i)).collect();
        Ok(rt.heap.list_from(&items))
    });
    "list->vector", 1, Some(1), simple!(|rt, a| {
        match rt.heap.list_to_vec(a[0]) { Some(v) => Ok(rt.heap.vector_from(&v)), None => rt.type_error("a proper list", a[0]) }
    });
    "vector-fill!", 2, Some(2), simple!(|rt, a| {
        if !rt.heap.is_a(a[0], ObjType::Vector) { return rt.type_error("a vector", a[0]); }
        for i in 0..rt.heap.obj_len(a[0]) { rt.heap.obj_set(a[0], i, a[1]); }
        Ok(Value::UNSPECIFIED)
    });

    // ---- bytevectors ----
    "make-bytevector", 1, Some(2), simple!(|rt, a| {
        let n = int(rt, a[0])?;
        if n < 0 { return rt.fail("bytevector length must be non-negative", &[a[0]]); }
        let fill = if a.len() > 1 { int(rt, a[1])? } else { 0 };
        if !(0..=255).contains(&fill) { return rt.fail("byte out of range", &[a[1]]); }
        Ok(rt.heap.make_bytevector(&vec![fill as u8; n as usize]))
    });
    "bytevector", 0, None, simple!(|rt, a| {
        let mut bytes = Vec::with_capacity(a.len());
        for (i, x) in a.iter().copied().enumerate() {
            let b = int(rt, x)?;
            if !(0..=255).contains(&b) { return rt.fail("byte out of range", &[a[i]]); }
            bytes.push(b as u8);
        }
        Ok(rt.heap.make_bytevector(&bytes))
    });
    "bytevector-length", 1, Some(1), simple!(|rt, a| {
        if !rt.heap.is_a(a[0], ObjType::Bytevector) { return rt.type_error("a bytevector", a[0]); }
        Ok(Value::fixnum(rt.heap.bytevector_len(a[0]) as i64))
    });
    "bytevector-u8-ref", 2, Some(2), simple!(|rt, a| {
        if !rt.heap.is_a(a[0], ObjType::Bytevector) { return rt.type_error("a bytevector", a[0]); }
        let n = rt.heap.bytevector_len(a[0]);
        let i = index(rt, a[1], n, "bytevector")?;
        Ok(Value::fixnum(rt.heap.bytevector_ref(a[0], i) as i64))
    });
    "bytevector-u8-set!", 3, Some(3), simple!(|rt, a| {
        if !rt.heap.is_a(a[0], ObjType::Bytevector) { return rt.type_error("a bytevector", a[0]); }
        let n = rt.heap.bytevector_len(a[0]);
        let i = index(rt, a[1], n, "bytevector")?;
        let b = int(rt, a[2])?;
        if !(0..=255).contains(&b) { return rt.fail("byte out of range", &[a[2]]); }
        rt.heap.bytevector_set(a[0], i, b as u8);
        Ok(Value::UNSPECIFIED)
    });

    // ---- errors ----
    "error", 1, None, simple!(|rt, a| {
        let msg = get_string(rt, a[0])?;
        let obj = rt.error_object(&msg, &a[1..]);
        Err(crate::error::Thrown::raise(obj))
    });
    "error-object?", 1, Some(1), simple!(|rt, a| Ok(Value::boolean(rt.is_error_object(a[0]))));
    "error-object-message", 1, Some(1), simple!(|rt, a| {
        if !rt.is_error_object(a[0]) { return rt.type_error("an error object", a[0]); }
        Ok(rt.heap.obj_ref(a[0], 1))
    });
    "error-object-irritants", 1, Some(1), simple!(|rt, a| {
        if !rt.is_error_object(a[0]) { return rt.type_error("an error object", a[0]); }
        Ok(rt.heap.obj_ref(a[0], 2))
    });

    // ---- records (the substrate for define-record-type) ----
    "%make-record-type", 2, Some(2), simple!(|rt, a| {
        if !rt.heap.is_a(a[0], ObjType::Symbol) { return rt.type_error("a symbol", a[0]); }
        let names = match rt.heap.list_to_vec(a[1]) { Some(v) => v, None => return rt.type_error("a list of field names", a[1]) };
        let fields = rt.heap.vector_from(&names);
        let rtd = rt.heap.alloc(ObjType::RecordType, 2, Value::UNSPECIFIED);
        rt.heap.obj_set(rtd, 0, a[0]);
        rt.heap.obj_set(rtd, 1, fields);
        Ok(rtd)
    });
    "%record", 1, None, simple!(|rt, a| {
        if !rt.heap.is_a(a[0], ObjType::RecordType) { return rt.type_error("a record type", a[0]); }
        let obj = rt.heap.alloc(ObjType::Record, a.len(), Value::UNSPECIFIED);
        for (i, v) in a.iter().enumerate() { rt.heap.obj_set(obj, i, *v); }
        Ok(obj)
    });
    "%record-of-type?", 2, Some(2), simple!(|rt, a| {
        Ok(Value::boolean(rt.heap.is_a(a[0], ObjType::Record)
            && rt.heap.obj_len(a[0]) >= 1
            && rt.heap.obj_ref(a[0], 0) == a[1]))
    });
    "%record-ref", 3, Some(3), simple!(|rt, a| {
        if !(rt.heap.is_a(a[0], ObjType::Record) && rt.heap.obj_len(a[0]) >= 1 && rt.heap.obj_ref(a[0], 0) == a[1]) {
            return rt.type_error("a record of the expected type", a[0]);
        }
        let n = rt.heap.obj_len(a[0]);
        let i = index(rt, a[2], n - 1, "record field")?;
        Ok(rt.heap.obj_ref(a[0], i + 1))
    });
    "%record-set!", 4, Some(4), simple!(|rt, a| {
        if !(rt.heap.is_a(a[0], ObjType::Record) && rt.heap.obj_len(a[0]) >= 1 && rt.heap.obj_ref(a[0], 0) == a[1]) {
            return rt.type_error("a record of the expected type", a[0]);
        }
        let n = rt.heap.obj_len(a[0]);
        let i = index(rt, a[2], n - 1, "record field")?;
        rt.heap.obj_set(a[0], i + 1, a[3]);
        Ok(Value::UNSPECIFIED)
    });

    // ---- ports ----
    "%open-input-file", 1, Some(1), simple!(|rt, a| {
        let name = get_string(rt, a[0])?;
        let path = rt.file_base.join(&name);
        match std::fs::read_to_string(&path) {
            Ok(text) => Ok(crate::port::make_input_port(rt, &name, &text)),
            Err(e) => rt.fail(&format!("cannot open {}: {e}", path.display()), &[a[0]]),
        }
    });
    "%standard-output", 0, Some(0), simple!(|rt, a| { let _ = &a; Ok(crate::port::make_stdout_port(rt)) });
    "%port?", 1, Some(1), simple!(|rt, a| Ok(Value::boolean(rt.heap.is_a(a[0], ObjType::Port))));
    "%port-read-char", 1, Some(1), simple!(|rt, a| crate::port::read_char(rt, a[0], true));
    "%port-peek-char", 1, Some(1), simple!(|rt, a| crate::port::read_char(rt, a[0], false));
    "%port-at-eof?", 1, Some(1), simple!(|rt, a| {
        let eof = crate::port::at_eof(rt, a[0])?;
        Ok(Value::boolean(eof))
    });
    "%port-read-datum", 1, Some(2), simple!(|rt, a| {
        let fold = a.len() > 1 && a[1].is_true();
        crate::port::read_datum(rt, a[0], fold)
    });
    "%port-write-string", 2, Some(2), simple!(|rt, a| {
        let text = get_string(rt, a[1])?;
        crate::port::write_string(rt, a[0], &text)
    });
    "%datum->string", 1, Some(1), simple!(|rt, a| {
        let text = display_value(&rt.heap, a[0]);
        Ok(rt.heap.make_string(&text))
    });
    "%close-port", 1, Some(1), simple!(|rt, a| {
        let _ = &rt;
        let _ = &a;
        Ok(Value::UNSPECIFIED)
    });

    // ---- output ----
    "display", 1, Some(2), simple!(|rt, a| { let s = display_value(&rt.heap, a[0]); rt.emit(&s); Ok(Value::UNSPECIFIED) });
    "write",   1, Some(2), simple!(|rt, a| { let s = write_value(&rt.heap, a[0]); rt.emit(&s); Ok(Value::UNSPECIFIED) });
    "newline", 0, Some(1), simple!(|rt, a| { let _ = &a; rt.emit("\n"); Ok(Value::UNSPECIFIED) });
    "write-string", 1, Some(2), simple!(|rt, a| { let s = get_string(rt, a[0])?; rt.emit(&s); Ok(Value::UNSPECIFIED) });
    "write-char", 1, Some(2), simple!(|rt, a| { let c = get_char(rt, a[0])?; rt.emit(&c.to_string()); Ok(Value::UNSPECIFIED) });

    // ---- engine operations ----
    "apply",            1, None,    PrimKind::Engine(EngineOp::Apply);
    "%call/cc",         1, Some(1), PrimKind::Engine(EngineOp::CallCC);
    "values",           0, None,    PrimKind::Engine(EngineOp::Values);
    "call-with-values", 2, Some(2), PrimKind::Engine(EngineOp::CallWithValues);

    // ---- the floor of the condition system ----
    // Reached only when the prelude's `raise` finds no handler installed; the
    // engine turns this into a real abort rather than another Scheme raise,
    // which is what stops the obvious infinite regress.
    "%raise-uncaught", 1, Some(1), simple!(|rt, a| {
        let _ = &rt;
        Err(crate::error::Thrown::fatal(a[0]))
    });

    // ---- promises ----
    // `delay` and `delay-force` expand to these; `force` is an engine
    // operation because forcing re-enters evaluation.
    "%make-promise-thunk", 1, Some(1), simple!(|rt, a| Ok(make_promise(rt, PROMISE_THUNK, a[0])));
    "%make-promise-lazy",  1, Some(1), simple!(|rt, a| Ok(make_promise(rt, PROMISE_LAZY, a[0])));
    "make-promise", 1, Some(1), simple!(|rt, a| {
        // R7RS: an already-made promise is returned unchanged.
        if rt.heap.is_a(a[0], ObjType::Promise) { return Ok(a[0]); }
        Ok(make_promise(rt, PROMISE_FORCED, a[0]))
    });
    "promise?", 1, Some(1), simple!(|rt, a| Ok(Value::boolean(rt.heap.is_a(a[0], ObjType::Promise))));
    "%promise-state", 1, Some(1), simple!(|rt, a| {
        if !rt.heap.is_a(a[0], ObjType::Promise) { return rt.type_error("a promise", a[0]); }
        Ok(rt.heap.obj_ref(a[0], 0))
    });
    "%promise-value", 1, Some(1), simple!(|rt, a| {
        if !rt.heap.is_a(a[0], ObjType::Promise) { return rt.type_error("a promise", a[0]); }
        Ok(rt.heap.obj_ref(a[0], 1))
    });
    "%promise-set-forced!", 2, Some(2), simple!(|rt, a| {
        if !rt.heap.is_a(a[0], ObjType::Promise) { return rt.type_error("a promise", a[0]); }
        rt.heap.obj_set(a[0], 0, Value::fixnum(PROMISE_FORCED));
        rt.heap.obj_set(a[0], 1, a[1]);
        Ok(Value::UNSPECIFIED)
    });

    // ---- boxes ----
    // Assignment conversion's cells. Reached only through `Node::PrimCall`,
    // never through a global, so redefining `vector-ref` cannot break `set!`.
    // ---- bloblets (`docs/object-model.md`) ----
    // Fields are named by `k`, their negative offset from the suffix; field
    // 1 is the trailer, so a bloblet made here has fields 2 through F. Any
    // bloblet can be read; only plain ones (kind `bloblet`) written, so the
    // engines' own objects cannot be changed from here.
    "%make-bloblet", 1, None, simple!(|rt, a| {
        let bytes = int(rt, a[0])?;
        if !(0..=u32::MAX as i64).contains(&bytes) { return rt.fail("a bloblet's suffix is 0 to 4 GiB", &[a[0]]); }
        let n = a.len() - 1;
        let b = rt.heap.make_bloblet(PLAIN_BLOBLET, n, bytes as usize, true);
        for (i, v) in a[1..].iter().enumerate() {
            rt.heap.set_bloblet_slot(b, i + 2, *v);
        }
        Ok(b)
    });
    "%make-bloblet-filled", 3, Some(3), simple!(|rt, a| {
        let bytes = int(rt, a[0])?;
        let n = int(rt, a[1])?;
        if !(0..=u32::MAX as i64).contains(&bytes) { return rt.fail("a bloblet's suffix is 0 to 4 GiB", &[a[0]]); }
        if !(0..1 << 40).contains(&n) { return rt.fail("a bloblet's field count must be non-negative", &[a[1]]); }
        let b = rt.heap.make_bloblet(PLAIN_BLOBLET, n as usize, bytes as usize, true);
        for k in 2..n as usize + 2 {
            rt.heap.set_bloblet_slot(b, k, a[2]);
        }
        Ok(b)
    });
    // FNV-1a over the characters, kept to a non-negative fixnum: the same
    // string always hashes the same, across runs and collections.
    // FX-26's standard operations that Scheme runs as procedures of its
    // own: primitives here, so that cellular code can call them too.
    "%fx26-char-in?", 2, Some(2), simple!(|rt, a| {
        let c = get_char(rt, a[0])?;
        let s = get_string(rt, a[1])?;
        Ok(Value::boolean(s.contains(c)))
    });
    // The fixed-width integers, `i32`, `u32`, `i64`, `u64` (PLAN.md, Q2 b):
    // wrapping arithmetic, on values that are the integers they stand for.
    "%fx26-i32+", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "add", Width::I32));
    "%fx26-i32-", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "sub", Width::I32));
    "%fx26-i32*", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "mul", Width::I32));
    "%fx26-i32-quotient", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "quot", Width::I32));
    "%fx26-i32-remainder", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "rem", Width::I32));
    "%fx26-i32-and", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "and", Width::I32));
    "%fx26-i32-or", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "or", Width::I32));
    "%fx26-i32-xor", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "xor", Width::I32));
    "%fx26-i32<", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "lt", Width::I32));
    "%fx26-i32<=", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "le", Width::I32));
    "%fx26-i32>", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "gt", Width::I32));
    "%fx26-i32>=", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "ge", Width::I32));
    "%fx26-i32=", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "eq", Width::I32));
    "%fx26-i32-shl", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "shl", Width::I32));
    "%fx26-i32-shr", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "shr", Width::I32));
    "%fx26-i32-not", 1, Some(1), simple!(|rt, a| fixed_op(rt, a, "not", Width::I32));
    "%fx26-int->i32", 1, Some(1), simple!(|rt, a| fixed_op(rt, a, "from", Width::I32));
    "%fx26-i32->int", 1, Some(1), simple!(|rt, a| fixed_op(rt, a, "to", Width::I32));
    "%fx26-u32+", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "add", Width::U32));
    "%fx26-u32-", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "sub", Width::U32));
    "%fx26-u32*", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "mul", Width::U32));
    "%fx26-u32-quotient", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "quot", Width::U32));
    "%fx26-u32-remainder", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "rem", Width::U32));
    "%fx26-u32-and", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "and", Width::U32));
    "%fx26-u32-or", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "or", Width::U32));
    "%fx26-u32-xor", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "xor", Width::U32));
    "%fx26-u32<", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "lt", Width::U32));
    "%fx26-u32<=", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "le", Width::U32));
    "%fx26-u32>", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "gt", Width::U32));
    "%fx26-u32>=", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "ge", Width::U32));
    "%fx26-u32=", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "eq", Width::U32));
    "%fx26-u32-shl", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "shl", Width::U32));
    "%fx26-u32-shr", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "shr", Width::U32));
    "%fx26-u32-not", 1, Some(1), simple!(|rt, a| fixed_op(rt, a, "not", Width::U32));
    "%fx26-int->u32", 1, Some(1), simple!(|rt, a| fixed_op(rt, a, "from", Width::U32));
    "%fx26-u32->int", 1, Some(1), simple!(|rt, a| fixed_op(rt, a, "to", Width::U32));
    "%fx26-i64+", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "add", Width::I64));
    "%fx26-i64-", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "sub", Width::I64));
    "%fx26-i64*", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "mul", Width::I64));
    "%fx26-i64-quotient", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "quot", Width::I64));
    "%fx26-i64-remainder", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "rem", Width::I64));
    "%fx26-i64-and", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "and", Width::I64));
    "%fx26-i64-or", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "or", Width::I64));
    "%fx26-i64-xor", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "xor", Width::I64));
    "%fx26-i64<", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "lt", Width::I64));
    "%fx26-i64<=", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "le", Width::I64));
    "%fx26-i64>", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "gt", Width::I64));
    "%fx26-i64>=", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "ge", Width::I64));
    "%fx26-i64=", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "eq", Width::I64));
    "%fx26-i64-shl", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "shl", Width::I64));
    "%fx26-i64-shr", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "shr", Width::I64));
    "%fx26-i64-not", 1, Some(1), simple!(|rt, a| fixed_op(rt, a, "not", Width::I64));
    "%fx26-int->i64", 1, Some(1), simple!(|rt, a| fixed_op(rt, a, "from", Width::I64));
    "%fx26-i64->int", 1, Some(1), simple!(|rt, a| fixed_op(rt, a, "to", Width::I64));
    "%fx26-u64+", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "add", Width::U64));
    "%fx26-u64-", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "sub", Width::U64));
    "%fx26-u64*", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "mul", Width::U64));
    "%fx26-u64-quotient", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "quot", Width::U64));
    "%fx26-u64-remainder", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "rem", Width::U64));
    "%fx26-u64-and", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "and", Width::U64));
    "%fx26-u64-or", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "or", Width::U64));
    "%fx26-u64-xor", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "xor", Width::U64));
    "%fx26-u64<", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "lt", Width::U64));
    "%fx26-u64<=", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "le", Width::U64));
    "%fx26-u64>", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "gt", Width::U64));
    "%fx26-u64>=", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "ge", Width::U64));
    "%fx26-u64=", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "eq", Width::U64));
    "%fx26-u64-shl", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "shl", Width::U64));
    "%fx26-u64-shr", 2, Some(2), simple!(|rt, a| fixed_op(rt, a, "shr", Width::U64));
    "%fx26-u64-not", 1, Some(1), simple!(|rt, a| fixed_op(rt, a, "not", Width::U64));
    "%fx26-int->u64", 1, Some(1), simple!(|rt, a| fixed_op(rt, a, "from", Width::U64));
    "%fx26-u64->int", 1, Some(1), simple!(|rt, a| fixed_op(rt, a, "to", Width::U64));
    // FX-26's `vlambda` (`%vlambda`): `f`, a procedure of one list, as a
    // variadic one, a cellular closure over `f` of the word `rest; free 0;
    // ttailcall 1`: however many arguments it is called with (the frame's
    // count), their list, given to `f` in its place. Its register code, for
    // native code, which passes the count in a register at every call:
    // `vargs; save 0; cellular rest 0; setreg 1; lexical 0; pop 0;
    // tailinvoke 1`.
    "%fx26-vlambda", 1, Some(1), simple!(|rt, a| {
        use fixpt_heap::layout::cellular::{routine, CLOSURE_FREE0, CLOSURE_WORD, WORD_TWIN};
        use fixpt_heap::layout::regcode::op;
        let f = |n: u64| Value::fixnum(n as i64);
        let cells = [f(routine("rest")), f(routine("free")), Value::fixnum(0), f(routine("ttailcall")), Value::fixnum(1)];
        let name = rt.heap.intern("vlambda");
        let word = match rt.heap.make_cellular_word(name, &cells) {
            Ok(w) => w,
            Err(e) => return rt.fail(&e, &[a[0]]),
        };
        let o = |n: &str| Value::fixnum(op(n) as i64);
        let (zero, one) = (Value::fixnum(0), Value::fixnum(1));
        let regs = [
            o("vargs"), o("save"), zero, o("cellular"), f(routine("rest")), zero, o("setreg"), one,
            o("lexical"), zero, o("pop"), zero, o("tailinvoke"), one,
        ];
        match rt.heap.make_register_word(name, word, &regs) {
            Ok(rw) => rt.heap.set_bloblet_slot(word, WORD_TWIN, rw),
            Err(e) => return rt.fail(&e, &[a[0]]),
        }
        let c = rt.heap.make_bloblet(fixpt_heap::layout::kind("cellular-closure"), 2, 0, true);
        rt.heap.set_bloblet_slot(c, CLOSURE_WORD, word);
        rt.heap.set_bloblet_slot(c, CLOSURE_FREE0, a[0]);
        Ok(c)
    });
    // FX-26's `string-compare`: -1, 0 or 1, as `a[0]` comes before, is, or
    // comes after `a[1]`, character by character.
    "%fx26-string-compare", 2, Some(2), simple!(|rt, a| {
        let (x, y) = (get_string(rt, a[0])?, get_string(rt, a[1])?);
        Ok(Value::fixnum(x.cmp(&y) as i64))
    });
    // FX-26's `symbol-compare`: the same, of two symbols' names.
    "%fx26-symbol-compare", 2, Some(2), simple!(|rt, a| {
        for s in [a[0], a[1]] {
            if !rt.heap.is_a(s, ObjType::Symbol) { return rt.type_error("a symbol", s); }
        }
        Ok(Value::fixnum(rt.heap.symbol_name(a[0]).cmp(&rt.heap.symbol_name(a[1])) as i64))
    });
    // FX-26's `string-search`: where `a[1]` first occurs in `a[0]` at or
    // after character `a[2]`, in characters; or -1.
    "%fx26-string-search", 3, Some(3), simple!(|rt, a| {
        let (s, sub, from) = (get_string(rt, a[0])?, get_string(rt, a[1])?, int(rt, a[2])?);
        let Some((start, _)) = s.char_indices().chain(std::iter::once((s.len(), ' '))).nth(from.max(0) as usize) else { return Ok(Value::fixnum(-1)) };
        Ok(Value::fixnum(s[start..].find(&sub).map_or(-1, |b| from.max(0) + s[start..start + b].chars().count() as i64)))
    });
    // FX-26's `+`, `-` and `*`: on fixnums, and failing past them ("integer
    // overflow"), as every machine's code does (PLAN.md, Q2).
    "%fx26-add", 2, Some(2), simple!(|rt, a| fx26_arith(rt, a, i64::checked_add));
    "%fx26-sub", 2, Some(2), simple!(|rt, a| fx26_arith(rt, a, i64::checked_sub));
    "%fx26-mul", 2, Some(2), simple!(|rt, a| fx26_arith(rt, a, i64::checked_mul));
    // And `quotient`: the least fixnum's by −1 is past one.
    "%fx26-quotient", 2, Some(2), simple!(|rt, a| {
        if a[1] == Value::fixnum(0) {
            return rt.fail("division by zero", &[a[0], a[1]]);
        }
        fx26_arith(rt, a, i64::checked_div)
    });
    // FX-26's `parse-number`: the number `a[0]` spells in radix `a[1]`
    // (2 to 36), sign and all, in a list; or none.
    "%fx26-parse-number", 2, Some(2), simple!(|rt, a| {
        let s = get_string(rt, a[0])?;
        let radix = radix(rt, a[1])?;
        match fixpt_read::reader::parse_number(&s, radix, None) {
            Some(n) => { let v = crate::num_from_literal(rt, &n); Ok(rt.heap.cons(v, Value::NULL)) }
            None => Ok(Value::NULL),
        }
    });
    // FX-26's `parse-nat`: the natural number `a[0]` spells in radix
    // `a[1]` (2 to 36); or -1, for anything else (a sign included: signed
    // numbers are `parse-number`'s).
    "%fx26-parse-nat", 2, Some(2), simple!(|rt, a| {
        let s = get_string(rt, a[0])?;
        let radix = radix(rt, a[1])?;
        let n = fixpt_read::reader::parse_number(&s, radix, None).map(|n| crate::num_from_literal(rt, &n));
        Ok(match n { Some(v) if v.is_fixnum() && v.as_fixnum() >= 0 => v, _ => Value::fixnum(-1) })
    });
    "%fx26-bytevector", 1, Some(1), simple!(|rt, a| {
        let Some(items) = rt.heap.list_to_vec(a[0]) else { return rt.type_error("a list", a[0]) };
        let mut bytes = Vec::with_capacity(items.len());
        for x in items {
            let b = int(rt, x)?;
            if !(0..=255).contains(&b) { return rt.fail("byte out of range", &[x]); }
            bytes.push(b as u8);
        }
        Ok(rt.heap.make_bytevector(&bytes))
    });
    "%fx26-byte?", 1, Some(1), simple!(|_rt, a| Ok(Value::boolean(a[0].is_fixnum() && (0..=255).contains(&a[0].as_fixnum()))));
    "%fx26-fixnum?", 1, Some(1), simple!(|_rt, a| Ok(Value::boolean(a[0].is_fixnum())));
    // FX-26's `nat?`: an integer no less than 0.
    "%fx26-nat?", 1, Some(1), simple!(|_rt, a| Ok(Value::boolean(a[0].is_fixnum() && a[0].as_fixnum() >= 0)));
    "%fx26-unit-cell", 0, Some(0), simple!(|rt, _a| Ok(rt.heap.intern("#u")));
    "%fx26-nil-cell", 0, Some(0), simple!(|_rt, _a| Ok(Value::NULL));
    // A constant sum or product, made while compiling (`wcell-sum`,
    // `wcell-product`): a sum of tag `a[0]` and value `a[1]`; a product of
    // the list `a[0]`'s cells, in order.
    // A lifted procedure's closure, over nothing, made while compiling
    // (`wcell-closure`), and its word set once compiled (`close-over-word!`).
    "%fx26-closure-cell", 0, Some(0), simple!(|rt, _a| Ok(rt.heap.closure_over_nothing()));
    "%fx26-close-over-word!", 2, Some(2), simple!(|rt, a| {
        rt.heap.set_bloblet_slot(a[0], fixpt_heap::layout::cellular::CLOSURE_WORD, a[1]);
        Ok(rt.heap.intern("#u"))
    });
    // A procedure converted to a convention (`docs/research/native-conventions.md`):
    // `a[1]` is its arity times 4, plus 1 for `cellular` or 2 for `native`.
    // A procedure already of that convention is itself; one of the other,
    // an adapter (`Runtime::adapt`); anything else is itself, as every
    // machine's call looks at its callee's kind.
    "%fx26-convert", 2, Some(2), simple!(|rt, a| {
        let (f, code) = (a[0], a[1].as_fixnum());
        let native = code & 3 == 2;
        let is = |rt: &Runtime, k: &str| f.is_bloblet() && rt.heap.bloblet_kind(f) == fixpt_heap::layout::kind(k);
        let (cellular, is_native) = (is(rt, "cellular-closure") || is(rt, "cellular-continuation"), is(rt, "native-closure"));
        if (native && cellular) || (!native && is_native) {
            let Some(adapt) = rt.adapt else {
                return rt.fail("no procedure of the other convention can be made here", &[f]);
            };
            return match adapt(rt, f, (code >> 2) as usize, native) {
                Ok(v) => Ok(v),
                Err(m) => rt.fail(&m, &[f]),
            };
        }
        Ok(f)
    });
    "%fx26-sum-cell", 2, Some(2), simple!(|rt, a| Ok(rt.heap.make_frozen(SUM_KIND, &a[..2])));
    "%fx26-product-cell", 1, Some(1), simple!(|rt, a| {
        let Some(items) = rt.heap.list_to_vec(a[0]) else { return rt.type_error("a list", a[0]) };
        Ok(rt.heap.make_frozen(PRODUCT_KIND, &items))
    });
    // A global's cell: a plain bloblet whose field 2 is the value and whose
    // field 3 is its name, for showing (`%disassemble`). Until its
    // definition runs it holds a procedure that traps when called. A checked
    // program never calls it then; if a compiler's mistake did, a typed call
    // would still meet a closure, and trap.
    "%fx26-make-global", 1, Some(1), simple!(|rt, a| {
        let undefined = rt.heap.undefined_closure();
        let b = rt.heap.make_bloblet(PLAIN_BLOBLET, 2, 0, true);
        rt.heap.set_bloblet_slot(b, 2, undefined);
        rt.heap.set_bloblet_slot(b, 3, a[0]);
        Ok(b)
    });
    // An I-cell (Arvind's I-structures): a plain bloblet whose field 2 says
    // whether it is full and whose field 3 is its value. Written once; read
    // only when full. Nothing else can fill it in a sequential run, so a
    // read of an empty cell, which would wait forever, is an error.
    "%fx26-make-icell", 0, Some(0), simple!(|rt, _a| {
        let b = rt.heap.make_bloblet(PLAIN_BLOBLET, 2, 0, true);
        rt.heap.set_bloblet_slot(b, 2, Value::FALSE);
        rt.heap.set_bloblet_slot(b, 3, Value::FALSE);
        Ok(b)
    });
    "%fx26-icell-put!", 2, Some(2), simple!(|rt, a| {
        if !a[0].is_bloblet() { return rt.type_error("an i-cell", a[0]) }
        if rt.heap.bloblet_slot(a[0], 2) != Value::FALSE {
            return rt.fail("an i-cell written twice", &[a[1]]);
        }
        rt.heap.set_bloblet_slot(a[0], 3, a[1]);
        rt.heap.set_bloblet_slot(a[0], 2, Value::TRUE);
        Ok(rt.heap.intern("#u"))
    });
    "%fx26-icell-get", 1, Some(1), simple!(|rt, a| {
        if !a[0].is_bloblet() { return rt.type_error("an i-cell", a[0]) }
        if rt.heap.bloblet_slot(a[0], 2) == Value::FALSE {
            return rt.fail("an i-cell read before it was written", &[]);
        }
        Ok(rt.heap.bloblet_slot(a[0], 3))
    });
    // A cellular word or closure's code, shown: every word it reaches.
    "%disassemble", 1, Some(1), simple!(|rt, a| {
        let asm = if rt.show_machine_code { rt.machine_code } else { None };
        let native = a[0].is_bloblet() && rt.heap.bloblet_kind(a[0]) == fixpt_heap::layout::kind("native-closure");
        // A native closure: the cellular word it was compiled from, or,
        // asked for machine code (`,disassemble-asm`), its machine code.
        let source = crate::disasm::native_source(&rt.heap, a[0]).filter(|_| native && !rt.show_machine_code);
        let s = match (source, rt.native_code.filter(|_| native).and_then(|f| f(&rt.heap, a[0]))) {
            (Some(text), _) => text,
            (None, Some(s)) => s,
            (None, None) => crate::disasm::disassemble_with(&rt.heap, a[0], asm),
        };
        Ok(rt.heap.make_string(&s))
    });
    "%fx26-string-downcase", 1, Some(1), simple!(|rt, a| { let s = get_string(rt, a[0])?; Ok(rt.heap.make_string(&s.to_lowercase())) });
    "%fx26-string-ci=?", 2, Some(2), simple!(|rt, a| {
        let (x, y) = (get_string(rt, a[0])?, get_string(rt, a[1])?);
        Ok(Value::boolean(x.to_lowercase() == y.to_lowercase()))
    });
    "%fx26-string-copy", 1, Some(1), simple!(|rt, a| { let s = get_string(rt, a[0])?; Ok(rt.heap.make_string(&s)) });
    // A list copied; a cyclic one is an error (`list_to_vec` stops on a
    // cycle). Also `apply`'s, whose variadic procedure's rest list must be
    // fresh, as Scheme's is (R7RS 4.1.4, "newly allocated"): FX-26 types it
    // `acyclic`, which the caller's list, if it can be written, is not. A
    // cycle is an error, not a hang, as Racket makes it: `apply` says no
    // `spin`.
    "%fx26-list-copy", 1, Some(1), simple!(|rt, a| {
        let Some(items) = rt.heap.list_to_vec(a[0]) else { return rt.type_error("a list", a[0]) };
        Ok(rt.heap.list_from(&items))
    });
    // No cycle through pairs, vectors, or bloblets' fields: a depth-first
    // walk marking the path it is on and what it has finished, so sharing
    // is fine and only a way back to the path is a cycle. What FX-26's
    // `acyclic?` asks of data, whose storage is only these.
    "%fx26-acyclic?", 1, Some(1), simple!(|rt, a| {
        let h = &rt.heap;
        let kids = |v: Value| -> Vec<Value> {
            if v.is_pair() {
                vec![h.car(v), h.cdr(v)]
            } else if v.is_bloblet() {
                (1..=h.bloblet_head(v).fields).filter_map(|k| h.bloblet_field(v, k).ok()).collect()
            } else if h.is_a(v, ObjType::Vector) {
                (0..h.obj_len(v)).map(|i| h.obj_ref(v, i)).collect()
            } else {
                Vec::new()
            }
        };
        // 1: on the path; 2: finished.
        let mut mark: std::collections::HashMap<Value, u8> = std::collections::HashMap::new();
        let mut stack: Vec<(Value, Vec<Value>)> = vec![(a[0], kids(a[0]))];
        mark.insert(a[0], 1);
        while let Some((v, ks)) = stack.last_mut() {
            match ks.pop() {
                Some(k) => match mark.get(&k) {
                    Some(1) => return Ok(Value::FALSE),
                    Some(_) => {}
                    None => {
                        mark.insert(k, 1);
                        let kk = kids(k);
                        stack.push((k, kk));
                    }
                },
                None => {
                    mark.insert(*v, 2);
                    stack.pop();
                }
            }
        }
        Ok(Value::TRUE)
    });
    // The first of two: `certify-length`, which only retypes its value.
    "%fx26-first", 2, Some(2), simple!(|_rt, a| Ok(a[0]));
    // A proper list of exactly `n` elements: what FX-26's `confirm-length`
    // asks. A cyclic list is none (`list_to_vec` stops on a cycle).
    "%fx26-length-is?", 2, Some(2), simple!(|rt, a| {
        if !a[1].is_fixnum() { return rt.type_error("a fixnum", a[1]); }
        let n = a[1].as_fixnum();
        Ok(Value::boolean(rt.heap.list_to_vec(a[0]).is_some_and(|items| items.len() as i64 == n)))
    });
    // A proper list: ends in `()`, and has no cycle (tortoise and hare).
    "%fx26-list?", 1, Some(1), simple!(|rt, a| {
        let (mut slow, mut fast) = (a[0], a[0]);
        loop {
            for _ in 0..2 {
                if fast.is_null() { return Ok(Value::TRUE); }
                if !fast.is_pair() { return Ok(Value::FALSE); }
                fast = rt.heap.cdr(fast);
            }
            slow = rt.heap.cdr(slow);
            if slow == fast { return Ok(Value::FALSE); }
        }
    });
    // A cellular word's cells, looked at: for the compiler to machine code
    // written in FX-26. Words are frozen, so these are pure.
    "%tword-fields", 1, Some(1), simple!(|rt, a| {
        if !rt.heap.is_cellular_word(a[0]) { return rt.type_error("a cellular word", a[0]); }
        Ok(Value::fixnum(rt.heap.bloblet_head(a[0]).fields as i64))
    });
    "%tword-fixnum?", 2, Some(2), simple!(|rt, a| {
        if !rt.heap.is_cellular_word(a[0]) { return rt.type_error("a cellular word", a[0]); }
        let k = int(rt, a[1])?;
        let fields = rt.heap.bloblet_head(a[0]).fields as i64;
        Ok(Value::boolean((1..=fields).contains(&k) && rt.heap.bloblet_slot(a[0], k as usize).is_fixnum()))
    });
    "%tword-int", 2, Some(2), simple!(|rt, a| {
        if !rt.heap.is_cellular_word(a[0]) { return rt.type_error("a cellular word", a[0]); }
        let k = int(rt, a[1])?;
        let fields = rt.heap.bloblet_head(a[0]).fields as i64;
        let v = if (1..=fields).contains(&k) { rt.heap.bloblet_slot(a[0], k as usize) } else { Value::fixnum(0) };
        Ok(if v.is_fixnum() { v } else { Value::fixnum(0) })
    });
    "%string-hash", 1, Some(1), simple!(|rt, a| {
        let s = get_string(rt, a[0])?;
        let mut h: u64 = 0xcbf2_9ce4_8422_2325;
        for c in s.chars() {
            h ^= c as u64;
            h = h.wrapping_mul(0x0000_0100_0000_01b3);
        }
        Ok(Value::fixnum((h >> 4) as i64))
    });
    // FX-26's immutable data: a bloblet of kind `sum` or `product` with these
    // fields, frozen, fields and suffix, as it is made.
    "%make-frozen", 1, None, simple!(|rt, a| {
        let kind = int(rt, a[0])?;
        if kind != SUM_KIND as i64 && kind != PRODUCT_KIND as i64 {
            return rt.fail("%make-frozen makes sums and products", &[a[0]]);
        }
        Ok(rt.heap.make_frozen(kind as u8, &a[1..]))
    });
    // ---- cellular words (`layout::cellular`) ----
    // A word of `cells` (a list), checked as every word is
    // (`Heap::make_cellular_word`); `#!default` in a cell is the word itself.
    "%make-word", 2, Some(2), simple!(|rt, a| {
        let Some(cells) = rt.heap.list_to_vec(a[1]) else { return rt.type_error("a list of cells", a[1]) };
        match rt.heap.make_cellular_word(a[0], &cells) {
            Ok(w) => Ok(w),
            Err(e) => rt.fail(&format!("not a word: {e}"), &[a[0]]),
        }
    });
    // ---- the collector, observed ----
    // How many collections there have been, and how many words they copied:
    // for tests and tools that want to see the collector at work.
    // Collections made, minor and major.
    "%gc-count", 0, Some(0), simple!(|rt, _a| Ok(Value::fixnum(rt.heap.collections() as i64)));
    "%gc-words-copied", 0, Some(0), simple!(|rt, _a| Ok(Value::fixnum(rt.heap.words_copied as i64)));
    // Collect at every nth safepoint as well as when full; 0 for only when
    // full. For sweeping collections through a program to find rooting bugs.
    "%gc-every!", 1, Some(1), simple!(|rt, a| {
        let n = int(rt, a[0])?;
        if n < 0 { return rt.fail("%gc-every! takes a count, 0 or more", &[a[0]]); }
        rt.heap.gc_every = n as u64;
        Ok(Value::UNSPECIFIED)
    });
    // Larceny's SRO: a vector of every live object of a kind (a kind's name,
    // `pair`, or #f for any) reached by 1 to `limit` references (#f: any
    // number), traced from the heap's roots. An observer's tool: it sees
    // every region, so no language's standard environment has it.
    // Larceny's SRO: a vector of every live object of a kind (a kind's name,
    // `pair`, or #f for any) reached by 1 to `limit` references (#f: any
    // number), traced from the heap's roots and the engine's own stacks. An
    // observer's tool: it sees every region, so no language's standard
    // environment has it. The engine's, because only it has its stacks.
    "%sro", 2, Some(2), PrimKind::Engine(EngineOp::Sro);
    // The object that stands for the word being made in `%make-word`'s cells.
    "%default-object", 0, Some(0), simple!(|_rt, _a| Ok(Value::DEFAULT));
    // A primitive's number, for cellular code's `prim`, if it needs no
    // engine; -1 otherwise.
    "%runtime-primitive", 1, Some(1), simple!(|rt, a| {
        let name = get_string(rt, a[0])?;
        let n = PRIMITIVES.iter().position(|p| p.name == name && matches!(p.kind, PrimKind::Simple(_)));
        Ok(Value::fixnum(n.map_or(-1, |n| n as i64)))
    });
    // How many arguments the runtime primitive named `a[0]` takes, if it is
    // one `%runtime-primitive` finds and takes a fixed number; else -1.
    "%runtime-primitive-arity", 1, Some(1), simple!(|rt, a| {
        let name = get_string(rt, a[0])?;
        let p = PRIMITIVES.iter().find(|p| p.name == name && matches!(p.kind, PrimKind::Simple(_)));
        Ok(Value::fixnum(p.filter(|p| p.max == Some(p.min)).map_or(-1, |p| p.min as i64)))
    });
    // Run a word with the arguments in a list on its data stack; the value it
    // leaves on top.
    "%run-word", 2, Some(2), simple!(|rt, a| { let run = rt.run_word; run_word_by(rt, a, run) });
    // `%run-word` on the machine for the front end (`front_end_run_word`).
    "%run-front-end", 2, Some(2), simple!(|rt, a| { let run = rt.front_end_run_word.or(rt.run_word); run_word_by(rt, a, run) });

    "%bloblet?", 1, Some(1), simple!(|_rt, a| Ok(Value::boolean(a[0].is_bloblet())));
    "%bloblet-kind", 1, Some(1), simple!(|rt, a| {
        let b = bloblet(rt, a[0])?;
        Ok(Value::fixnum(rt.heap.bloblet_kind(b) as i64))
    });
    "%bloblet-fields", 1, Some(1), simple!(|rt, a| {
        let b = bloblet(rt, a[0])?;
        Ok(Value::fixnum(rt.heap.bloblet_head(b).fields as i64))
    });
    "%bloblet-bytes", 1, Some(1), simple!(|rt, a| {
        let b = bloblet(rt, a[0])?;
        Ok(Value::fixnum(rt.heap.bloblet_head(b).bytes as i64))
    });
    "%bloblet-ref", 2, Some(2), simple!(|rt, a| {
        let b = bloblet(rt, a[0])?;
        let k = int(rt, a[1])?;
        match usize::try_from(k).ok().map(|k| rt.heap.bloblet_field(b, k)) {
            Some(Ok(v)) => Ok(v),
            Some(Err(e)) => rt.fail(&format!("bloblet field: {e}"), &[a[0], a[1]]),
            None => rt.fail("bloblet field: no such field", &[a[0], a[1]]),
        }
    });
    "%bloblet-set!", 3, Some(3), simple!(|rt, a| {
        let b = plain_bloblet(rt, a[0])?;
        let k = int(rt, a[1])?;
        match usize::try_from(k).ok().map(|k| rt.heap.set_bloblet_field(b, k, a[2])) {
            Some(Ok(())) => Ok(Value::UNSPECIFIED),
            Some(Err(e)) => rt.fail(&format!("bloblet field: {e}"), &[a[0], a[1]]),
            None => rt.fail("bloblet field: no such field", &[a[0], a[1]]),
        }
    });
    "%bloblet-byte", 2, Some(2), simple!(|rt, a| {
        let b = bloblet(rt, a[0])?;
        let i = int(rt, a[1])?;
        match usize::try_from(i).ok().map(|i| rt.heap.bloblet_byte(b, i)) {
            Some(Ok(x)) => Ok(Value::fixnum(x as i64)),
            _ => rt.fail("bloblet byte: out of range", &[a[0], a[1]]),
        }
    });
    "%bloblet-set-byte!", 3, Some(3), simple!(|rt, a| {
        let b = plain_bloblet(rt, a[0])?;
        let i = int(rt, a[1])?;
        let x = int(rt, a[2])?;
        let Ok(x) = u8::try_from(x) else { return rt.fail("bloblet byte: not a byte", &[a[2]]) };
        match usize::try_from(i).ok().map(|i| rt.heap.set_bloblet_byte(b, i, x)) {
            Some(Ok(())) => Ok(Value::UNSPECIFIED),
            Some(Err(e)) => rt.fail(&format!("bloblet byte: {e}"), &[a[0], a[1]]),
            None => rt.fail("bloblet byte: out of range", &[a[0], a[1]]),
        }
    });
    "%bloblet-freeze!", 3, Some(3), simple!(|rt, a| {
        let b = plain_bloblet(rt, a[0])?;
        rt.heap.freeze_bloblet(b, a[1].is_true(), a[2].is_true());
        Ok(Value::UNSPECIFIED)
    });
    "%bloblet-frozen?", 1, Some(1), simple!(|rt, a| {
        let b = bloblet(rt, a[0])?;
        let h = rt.heap.bloblet_head(b);
        Ok(rt.heap.cons(Value::boolean(h.fields_frozen), Value::boolean(h.suffix_frozen)))
    });

    "%make-box", 1, Some(1), simple!(|rt, a| {
        let b = rt.heap.alloc(ObjType::Box, 1, Value::UNSPECIFIED);
        rt.heap.obj_set(b, 0, a[0]);
        Ok(b)
    });
    "%box-ref", 1, Some(1), simple!(|rt, a| Ok(rt.heap.obj_ref(a[0], 0)));
    "%box-set!", 2, Some(2), simple!(|rt, a| {
        rt.heap.obj_set(a[0], 0, a[1]);
        Ok(Value::UNSPECIFIED)
    });

    // ---- continuation marks, prompts, composable continuations ----
    "%wcm",               3, Some(3), PrimKind::Engine(EngineOp::WithMark);
    "%wind",              2, Some(2), PrimKind::Engine(EngineOp::Wind);
    "%prompt",            3, Some(3), PrimKind::Engine(EngineOp::Prompt);
    "%current-marks",     1, Some(1), PrimKind::Engine(EngineOp::CurrentMarks);
    "%first-mark",        3, Some(3), PrimKind::Engine(EngineOp::FirstMark);
    "%current-winders",   0, Some(0), PrimKind::Engine(EngineOp::CurrentWinders);
    "%prompt-available?", 1, Some(1), PrimKind::Engine(EngineOp::PromptAvailable);
    "%abort",             3, Some(3), PrimKind::Engine(EngineOp::Abort);
    "%call/comp",         2, Some(2), PrimKind::Engine(EngineOp::CallComposable);
    "%throw",             2, Some(2), PrimKind::Engine(EngineOp::Throw);
    "%host",              1, None,    PrimKind::Engine(EngineOp::Host);
    // A captured continuation carries its marks, so reading them needs no
    // engine: the encoding is shared (`cmarks`).
    "%continuation?", 1, Some(1), simple!(|rt, a| {
        Ok(Value::boolean(rt.heap.is_a(a[0], ObjType::Continuation)))
    });
    "%continuation-marks", 2, Some(2), simple!(|rt, a| {
        if !rt.heap.is_a(a[0], ObjType::Continuation) {
            return rt.type_error("a continuation", a[0]);
        }
        Ok(crate::cmarks::continuation_mark_list(&mut rt.heap, a[0], a[1]))
    });
    "%continuation-winders", 1, Some(1), simple!(|rt, a| {
        if !rt.heap.is_a(a[0], ObjType::Continuation) {
            return rt.type_error("a continuation", a[0]);
        }
        Ok(crate::cmarks::continuation_winder_list(&mut rt.heap, a[0]))
    });
    "%composable?", 1, Some(1), simple!(|rt, a| {
        Ok(Value::boolean(rt.heap.is_a(a[0], ObjType::Continuation)
            && crate::cmarks::is_composable(&rt.heap, a[0])))
    });
    // The identity. A prompt is installed by calling `%prompt` in *argument*
    // position of this, which guarantees it a frame of its own: a prompt that
    // shared its caller's frame would be removed by that frame's tail calls.
    "%prompt-result", 1, Some(1), simple!(|rt, a| { let _ = &rt; Ok(a[0]) });

    // ---- the REPL's hole ----
    // What `,help` inside a form becomes. Evaluating it reports the context it
    // was reached in, with the values that were actually computed on the way.
    "%hole", 2, Some(2), PrimKind::Engine(EngineOp::Hole);

    // ---- regions (`letrena`): the heap's, by handle ----
    // A handle is a fixnum; anything else (`#f`, a `letreap`'s for now)
    // means the heap. Leaving a region gives back the body's value.
    "%region-enter", 0, Some(0), simple!(|rt, _a| Ok(Value::fixnum(rt.heap.region_enter() as i64)));
    "%reap-enter", 0, Some(0), simple!(|rt, _a| Ok(Value::fixnum(rt.heap.reap_enter() as i64)));
    "%region-exit", 2, Some(2), simple!(|rt, a| {
        if a[0].is_fixnum() {
            rt.heap.region_exit(a[0].as_fixnum() as usize);
        }
        Ok(a[1])
    });
    "%region-cons", 3, Some(3), simple!(|rt, a| {
        let h = region_handle(a[0]);
        Ok(rt.heap.in_region(h, |heap| heap.cons(a[1], a[2])))
    });
    // As `%make-box`, `%make-bloblet-filled 0 n fill`, `%fx26-make-icell`
    // and `%make-bloblet`, in a region.
    "%region-new", 2, Some(2), simple!(|rt, a| {
        let h = region_handle(a[0]);
        Ok(rt.heap.in_region(h, |heap| {
            let b = heap.alloc(ObjType::Box, 1, Value::UNSPECIFIED);
            heap.obj_set(b, 0, a[1]);
            b
        }))
    });
    "%region-make-array", 3, Some(3), simple!(|rt, a| {
        let h = region_handle(a[0]);
        let n = int(rt, a[1])?;
        if !(0..1 << 40).contains(&n) { return rt.fail("a bloblet's field count must be non-negative", &[a[1]]); }
        Ok(rt.heap.in_region(h, |heap| {
            let b = heap.make_bloblet(PLAIN_BLOBLET, n as usize, 0, true);
            for k in 2..n as usize + 2 {
                heap.set_bloblet_slot(b, k, a[2]);
            }
            b
        }))
    });
    "%region-make-icell", 1, Some(1), simple!(|rt, a| {
        let h = region_handle(a[0]);
        Ok(rt.heap.in_region(h, |heap| {
            let b = heap.make_bloblet(PLAIN_BLOBLET, 2, 0, true);
            heap.set_bloblet_slot(b, 2, Value::FALSE);
            heap.set_bloblet_slot(b, 3, Value::FALSE);
            b
        }))
    });
    // The `closure` routine's closure, in a region: `h`, the free values in
    // order, then the word.
    "%region-closure", 2, None, simple!(|rt, a| {
        use fixpt_heap::layout::cellular::{CLOSURE_FREE0, CLOSURE_WORD};
        let h = region_handle(a[0]);
        let (w, free) = (a[a.len() - 1], &a[1..a.len() - 1]);
        Ok(rt.heap.in_region(h, |heap| {
            let c = heap.make_bloblet(fixpt_heap::layout::kind("cellular-closure"), free.len() + 1, 0, true);
            heap.set_bloblet_slot(c, CLOSURE_WORD, w);
            for (i, v) in free.iter().enumerate() {
                heap.set_bloblet_slot(c, CLOSURE_FREE0 + i, *v);
            }
            c
        }))
    });
    "%region-make-bloblet", 2, None, simple!(|rt, a| {
        let h = region_handle(a[0]);
        let bytes = int(rt, a[1])?;
        if !(0..=u32::MAX as i64).contains(&bytes) { return rt.fail("a bloblet's suffix is 0 to 4 GiB", &[a[1]]); }
        Ok(rt.heap.in_region(h, |heap| {
            let b = heap.make_bloblet(PLAIN_BLOBLET, a.len() - 2, bytes as usize, true);
            for (i, v) in a[2..].iter().enumerate() {
                heap.set_bloblet_slot(b, i + 2, *v);
            }
            b
        }))
    });
    // The hash `Heap::intern` kept with the symbol, of its name.
    "%symbol-hash", 1, Some(1), simple!(|rt, a| {
        if !rt.heap.is_a(a[0], ObjType::Symbol) { return rt.type_error("a symbol", a[0]); }
        Ok(rt.heap.obj_ref(a[0], 1))
    });
    // Register code (PLAN.md 13h′) for cellular word `a[0]`, from its cells:
    // made, checked, and set as the word's twin, as the Rust compiler does.
    "%set-register-twin", 2, Some(2), simple!(|rt, a| {
        let Some(cells) = rt.heap.list_to_vec(a[1]) else { return rt.type_error("a list of cells", a[1]) };
        let name = rt.heap.bloblet_slot(a[0], fixpt_heap::layout::cellular::WORD_NAME);
        match rt.heap.make_register_word(name, a[0], &cells) {
            Ok(rw) => {
                rt.heap.set_bloblet_slot(a[0], fixpt_heap::layout::cellular::WORD_TWIN, rw);
                Ok(rw)
            }
            Err(e) => rt.fail(&format!("not register code: {e}"), &[a[0]]),
        }
    });    // Its argument: FX-26's `stay-cellular`, which the native convention's
    // compiler declines by design (`fixpt_native::direct`), so that a
    // procedure calling it runs as cellular code, whatever that compiler
    // learns to do: a test's way to have some.
    "%stay-cellular", 1, Some(1), simple!(|_rt, a| Ok(a[0]));
}

/// Promise states. `[state, payload]`.
pub const PROMISE_THUNK: i64 = 0;
pub const PROMISE_FORCED: i64 = 1;
/// `delay-force`: the thunk yields another promise, which `force` must chain to
/// iteratively so that a recursive lazy computation runs in constant space.
pub const PROMISE_LAZY: i64 = 2;

pub fn make_promise(rt: &mut Runtime, state: i64, payload: Value) -> Value {
    let p = rt.heap.alloc(ObjType::Promise, 2, Value::UNSPECIFIED);
    rt.heap.obj_set(p, 0, Value::fixnum(state));
    rt.heap.obj_set(p, 1, payload);
    p
}

/// A region's handle, as `Heap::in_region` takes it: a fixnum's value, or,
/// for anything else (`#f`, the heap's), none that is live.
fn region_handle(v: Value) -> usize {
    if v.is_fixnum() { v.as_fixnum() as usize } else { usize::MAX }
}

fn string_chain(
    rt: &mut Runtime,
    args: &mut [Value],
    ok: impl Fn(std::cmp::Ordering) -> bool,
) -> Outcome<Value> {
    for i in 0..args.len().saturating_sub(1) {
        let a = get_string(rt, args[i])?;
        let b = get_string(rt, args[i + 1])?;
        if !ok(a.cmp(&b)) {
            return Ok(Value::FALSE);
        }
    }
    Ok(Value::TRUE)
}

/// Index of a primitive by name, for the expander to resolve against.
pub fn lookup(name: &str) -> Option<u16> {
    PRIMITIVES
        .iter()
        .position(|p| p.name == name)
        .map(|i| i as u16)
}

pub fn def(index: u16) -> &'static PrimDef {
    &PRIMITIVES[index as usize]
}
