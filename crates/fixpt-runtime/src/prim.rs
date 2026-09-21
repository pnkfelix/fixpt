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
/// Deliberately only four. `dynamic-wind`, `call/cc`'s winding wrapper,
/// `with-exception-handler`, `raise`, `raise-continuable` and `force` are all
/// *prelude Scheme* built on top of a raw, winding-unaware `%call/cc` — the
/// classic Dybvig arrangement. Written that way they are a dozen readable lines
/// each, they automatically get proper tail calls, and the engine never has to
/// reason about the interaction between winders and its own frame stack.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum EngineOp {
    Apply,
    /// Raw continuation capture: no `dynamic-wind` awareness at all.
    CallCC,
    Values,
    CallWithValues,
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
    "substring", 3, Some(3), simple!(|rt, a| {
        let s = get_string(rt, a[0])?;
        let chars: Vec<char> = s.chars().collect();
        let start = int(rt, a[1])?; let end = int(rt, a[2])?;
        if start < 0 || end < start || end as usize > chars.len() {
            return rt.fail("substring range out of bounds", &[a[1], a[2]]);
        }
        Ok(rt.heap.string_from_chars(&chars[start as usize..end as usize]))
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
