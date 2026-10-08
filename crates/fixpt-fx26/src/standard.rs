//! The initial environment.
//!
//! The memory operations have FX-87's types, from its standard environment
//! (`crates/fixpt-fx87/src/standard.fx`), less the trailing `@=` that FX-87
//! uses for the region of a variable's own binding, which the kernel does not
//! have. `cwcc` has the type PLDI '89 gives it (p. 4), binders written in
//! FX-87's parenthesised style.
//!
//! Lists are FX-87's: `(listof t r)` is `nil` or a pair whose tail is the
//! list again. `(pairof a b r)` is a pair, never `nil`; `(union nil (pairof a
//! b r))` is one that may be, which `null?` tests for, and the type the pair
//! operations take (`docs/fx26.md`, "Lists are FX-87's").
//!
//! The delimited-control operations are this project's (`docs/fx26.md`,
//! "Control, typed"). They keep SRFI 226's names where they mean the same
//! thing: `make-continuation-prompt-tag`, `abort-current-continuation`,
//! `call-with-composable-continuation` and `make-continuation-mark-key`.
//! `with-mark` takes a thunk where Scheme's `with-continuation-mark` is
//! syntax, and `first-mark`, `current-marks` and `marks-of` read marks.
//! Delimiting is the `prompt` form, not a constant: see `Checker`'s rule for
//! it.
//!
//! Characters, strings and comparisons are what the eager reader needs, with
//! Scheme's names. Strings are immutable here — nothing is given that could
//! change one — so making one is no effect. `datum` is a Scheme datum, as a
//! reader produces: opaque, built by the `datum-` operations and taken apart
//! by their inspectors, and immutable too, so building one is pure.

pub const ENTRIES: &[(&str, &str)] = &[
    ("new", "(poly ((r region)) (poly ((t type)) (subr (alloc r) (t) (ref t r))))"),
    ("get", "(poly ((r region)) (poly ((t type)) (subr (read r) ((ref t r)) t)))"),
    ("set", "(poly ((r region)) (poly ((t type)) (subr (write r) ((ref t r) t) unit)))"),
    ("cons", "(poly ((r region)) (poly ((t1 type) (t2 type)) (subr (alloc r) (t1 t2) (pairof t1 t2 r))))"),
    // `cons` in a region given as a value, which a `letrena` or `letreap`
    // binds: there, rather than in the heap.
    ("rcons", "(poly ((p place) (r region p)) (poly ((t1 type) (t2 type)) (subr (maxeff (alloc r) (alloc p)) ((place p) t1 t2) (pairof t1 t2 r))))"),
    ("rnew", "(poly ((p place) (r region p)) (poly ((t type)) (subr (maxeff (alloc r) (alloc p)) ((place p) t) (ref t r))))"),
    ("rmake-array", "(poly ((p place) (r region p)) (poly ((t type)) (subr (maxeff (alloc r) (alloc p)) ((place p) int t) (arrayof t r))))"),
    ("rmake-icell", "(poly ((p place) (r region p)) (poly ((t type)) (subr (maxeff (alloc r) (alloc p)) ((place p)) (icell t r))))"),
    ("car", "(poly ((r region)) (poly ((t1 type) (t2 type)) (subr (read r) ((union nil (pairof t1 t2 r))) t1)))"),
    ("cdr", "(poly ((r region)) (poly ((t1 type) (t2 type)) (subr (read r) ((union nil (pairof t1 t2 r))) t2)))"),
    // The identity, which the native convention's compiler declines: a
    // procedure calling it runs as cellular code.
    ("stay-cellular", "(poly ((t type)) (subr pure (t) t))"),
    ("set-car!", "(poly ((r region)) (poly ((t1 type) (t2 type)) (subr (write r) ((union nil (pairof t1 t2 r)) t1) unit)))"),
    ("set-cdr!", "(poly ((r region)) (poly ((t1 type) (t2 type)) (subr (write r) ((union nil (pairof t1 t2 r)) t2) unit)))"),
    // The empty list, of any element type at any region: `(proj nil @r
    // int)`. (It was any pair type, FX-87's `null ≤ pairof`, which `proj`
    // needed the tail's type for, the list's own; until PLAN Q7's `null`
    // and unions, `nil` is a list.)
    ("nil", "(poly ((r region) (t type)) (listof t r))"),
    // The absent pair: `nil`, at any pair type, for "a pair, or none" (a
    // table's entry, say). `nil`'s type until 2026-09-29.
    ("no-pair", "(poly ((r region) (t1 type) (t2 type)) (union nil (pairof t1 t2 r)))"),
    // The shape predicates (`check::SHAPES`): of any value, whether it has
    // the shape, which narrows a union (`docs/research/logical-types.md`).
    ("null?", "(poly ((t type)) (subr pure (t) (bool (then (shape 0 nil) (= (length 0) (lit 0))) (else (not (shape 0 nil)) (<= (lit 1) (length 0))))))"),
    ("pair?", "(poly ((t type)) (subr pure (t) (bool (then (shape 0 pair)) (else (not (shape 0 pair))))))"),
    ("int?", "(poly ((t type)) (subr pure (t) (bool (then (shape 0 int)) (else (not (shape 0 int))))))"),
    ("char?", "(poly ((t type)) (subr pure (t) (bool (then (shape 0 char)) (else (not (shape 0 char))))))"),
    ("bool?", "(poly ((t type)) (subr pure (t) (bool (then (shape 0 bool)) (else (not (shape 0 bool))))))"),
    ("string?", "(poly ((t type)) (subr pure (t) (bool (then (shape 0 string)) (else (not (shape 0 string))))))"),
    ("f64?", "(poly ((t type)) (subr pure (t) (bool (then (shape 0 f64)) (else (not (shape 0 f64))))))"),
    // What a quote builds, marked so (TODO §51): it interned, the one
    // object equal to it (`Heap::intern_datum`); which each compiler makes
    // once, as constant data, where it is all literals.
    ("%quote", "(poly ((t type)) (subr pure (t) t))"),
    ("vector?", "(poly ((t type)) (subr pure (t) (bool (then (shape 0 vector)) (else (not (shape 0 vector))))))"),
    ("bytevector?", "(poly ((t type)) (subr pure (t) (bool (then (shape 0 bytevector)) (else (not (shape 0 bytevector))))))"),
    ("symbol?", "(poly ((t type)) (subr pure (t) (bool (then (shape 0 symbol)) (else (not (shape 0 symbol))))))"),
    ("procedure?", "(poly ((t type)) (subr pure (t) (bool (then (shape 0 procedure)) (else (not (shape 0 procedure))))))"),
    ("array?", "(poly ((t type)) (subr pure (t) (bool (then (shape 0 bloblet)) (else (not (shape 0 bloblet))))))"),
    ("+", "(subr pure (int int) int)"),
    ("-", "(subr pure (int int) int)"),
    // A finite list's length, as a natural of its size.
    ("length", "(poly ((t type) (n size)) (subr pure ((nlist t n)) (nat n)))"),
    ("=", "(subr pure (int int) (bool (then (= 0 1)) (else (not (= 0 1)))))"),
    (
        "cwcc",
        "(poly ((r region)) (poly ((t type)) (poly ((e effect))
           (subr (maxeff (comefrom r) e)
                 ((subr e ((subr (goto r) (t) void)) t))
                 t))))",
    ),
    ("<", "(subr pure (int int) (bool (then (< 0 1)) (else (<= 1 0))))"),
    (">", "(subr pure (int int) (bool (then (< 1 0)) (else (<= 0 1))))"),
    ("<=", "(subr pure (int int) (bool (then (<= 0 1)) (else (< 1 0))))"),
    (">=", "(subr pure (int int) (bool (then (<= 1 0)) (else (< 0 1))))"),
    ("*", "(subr pure (int int) int)"),
    ("modulo", "(subr pure (int int) int)"),
    ("quotient", "(subr pure (int int) int)"),
    ("not", "(subr pure (bool) bool)"),
    ("char=?", "(subr pure (char char) bool)"),
    ("char-whitespace?", "(subr pure (char) bool)"),
    ("char-numeric?", "(subr pure (char) bool)"),
    ("char-alphabetic?", "(subr pure (char) bool)"),
    ("char-downcase", "(subr pure (char) char)"),
    ("char->integer", "(subr pure (char) int)"),
    ("integer->char", "(subr pure (int) char)"),
    ("char-in?", "(subr pure (char string) bool)"),
    ("string-append", "(subr pure (string string) string)"),
    // Lengths never below 0: naturals.
    ("string-length", "(subr pure (string) nat)"),
    ("string-ref", "(subr pure (string int) char)"),
    ("substring", "(subr pure (string int int) string)"),
    ("string=?", "(subr pure (string string) bool)"),
    // `f64`, IEEE binary64 (`docs/fx26.md`, "Floats").
    ("f64+", "(subr pure (f64 f64) f64)"),
    ("f64-", "(subr pure (f64 f64) f64)"),
    ("f64*", "(subr pure (f64 f64) f64)"),
    ("f64/", "(subr pure (f64 f64) f64)"),
    ("f64-min", "(subr pure (f64 f64) f64)"),
    ("f64-max", "(subr pure (f64 f64) f64)"),
    ("f64-atan2", "(subr pure (f64 f64) f64)"),
    ("f64-expt", "(subr pure (f64 f64) f64)"),
    // No propositions: with a NaN, `(not (< a b))` is not `(<= b a)`.
    ("f64<", "(subr pure (f64 f64) bool)"),
    ("f64<=", "(subr pure (f64 f64) bool)"),
    ("f64>", "(subr pure (f64 f64) bool)"),
    ("f64>=", "(subr pure (f64 f64) bool)"),
    ("f64=", "(subr pure (f64 f64) bool)"),
    ("f64-abs", "(subr pure (f64) f64)"),
    ("f64-neg", "(subr pure (f64) f64)"),
    ("f64-sqrt", "(subr pure (f64) f64)"),
    ("f64-floor", "(subr pure (f64) f64)"),
    ("f64-ceiling", "(subr pure (f64) f64)"),
    ("f64-truncate", "(subr pure (f64) f64)"),
    ("f64-round", "(subr pure (f64) f64)"),
    ("f64-exp", "(subr pure (f64) f64)"),
    ("f64-log", "(subr pure (f64) f64)"),
    ("f64-sin", "(subr pure (f64) f64)"),
    ("f64-cos", "(subr pure (f64) f64)"),
    ("f64-tan", "(subr pure (f64) f64)"),
    ("f64-asin", "(subr pure (f64) f64)"),
    ("f64-acos", "(subr pure (f64) f64)"),
    ("f64-atan", "(subr pure (f64) f64)"),
    ("f64-nan?", "(subr pure (f64) bool)"),
    ("f64-infinite?", "(subr pure (f64) bool)"),
    ("f64-finite?", "(subr pure (f64) bool)"),
    ("int->f64", "(subr pure (int) f64)"),
    ("f64->int", "(subr pure (f64) int)"),
    ("f64->string", "(subr pure (f64) string)"),
    ("string->f64", "(poly ((r region)) (subr (alloc r) (string) (listof f64 r)))"),
    // `f32`, IEEE binary32, an immediate (`docs/fx26.md`, "Floats").
    ("f32+", "(subr pure (f32 f32) f32)"),
    ("f32-", "(subr pure (f32 f32) f32)"),
    ("f32*", "(subr pure (f32 f32) f32)"),
    ("f32/", "(subr pure (f32 f32) f32)"),
    ("f32-min", "(subr pure (f32 f32) f32)"),
    ("f32-max", "(subr pure (f32 f32) f32)"),
    ("f32<", "(subr pure (f32 f32) bool)"),
    ("f32<=", "(subr pure (f32 f32) bool)"),
    ("f32>", "(subr pure (f32 f32) bool)"),
    ("f32>=", "(subr pure (f32 f32) bool)"),
    ("f32=", "(subr pure (f32 f32) bool)"),
    ("f32-abs", "(subr pure (f32) f32)"),
    ("f32-neg", "(subr pure (f32) f32)"),
    ("f32-sqrt", "(subr pure (f32) f32)"),
    ("f32-floor", "(subr pure (f32) f32)"),
    ("f32-ceiling", "(subr pure (f32) f32)"),
    ("f32-truncate", "(subr pure (f32) f32)"),
    ("f32-round", "(subr pure (f32) f32)"),
    ("f32-nan?", "(subr pure (f32) bool)"),
    ("f32-infinite?", "(subr pure (f32) bool)"),
    ("f32-finite?", "(subr pure (f32) bool)"),
    ("int->f32", "(subr pure (int) f32)"),
    ("f32->int", "(subr pure (f32) int)"),
    ("f32->string", "(subr pure (f32) string)"),
    ("f32->f64", "(subr pure (f32) f64)"),
    ("f64->f32", "(subr pure (f64) f32)"),
    // Flat arrays (Q6): made by a layout, the elements raw.
    ("make-flatarray", "(poly ((r region)) (poly ((t type)) (subr (alloc r) ((flatlayout t) int t) (flatarrayof t r))))"),
    ("flatarray-ref", "(poly ((r region)) (poly ((t type)) (subr (read r) ((flatarrayof t r) int) t)))"),
    ("flatarray-set!", "(poly ((r region)) (poly ((t type)) (subr (write r) ((flatarrayof t r) int t) unit)))"),
    ("flatarray-length", "(poly ((r region)) (poly ((t type)) (subr pure ((flatarrayof t r)) nat)))"),
    ("i32-flat", "(subr pure () (flatlayout i32))"),
    ("u32-flat", "(subr pure () (flatlayout u32))"),
    ("i64-flat", "(subr pure () (flatlayout i64))"),
    ("u64-flat", "(subr pure () (flatlayout u64))"),
    ("f32-flat", "(subr pure () (flatlayout f32))"),
    ("f64-flat", "(subr pure () (flatlayout f64))"),
    // The fixed-width integers (PLAN.md, Q2 b): wrapping arithmetic.
    ("i32+", "(subr pure (i32 i32) i32)"),
    ("i32-", "(subr pure (i32 i32) i32)"),
    ("i32*", "(subr pure (i32 i32) i32)"),
    ("i32-quotient", "(subr pure (i32 i32) i32)"),
    ("i32-remainder", "(subr pure (i32 i32) i32)"),
    ("i32-and", "(subr pure (i32 i32) i32)"),
    ("i32-or", "(subr pure (i32 i32) i32)"),
    ("i32-xor", "(subr pure (i32 i32) i32)"),
    ("i32<", "(subr pure (i32 i32) (bool (then (< 0 1)) (else (<= 1 0))))"),
    ("i32<=", "(subr pure (i32 i32) (bool (then (<= 0 1)) (else (< 1 0))))"),
    ("i32>", "(subr pure (i32 i32) (bool (then (< 1 0)) (else (<= 0 1))))"),
    ("i32>=", "(subr pure (i32 i32) (bool (then (<= 1 0)) (else (< 0 1))))"),
    ("i32=", "(subr pure (i32 i32) (bool (then (= 0 1)) (else (not (= 0 1)))))"),
    ("i32-shl", "(subr pure (i32 int) i32)"),
    ("i32-shr", "(subr pure (i32 int) i32)"),
    ("i32-not", "(subr pure (i32) i32)"),
    ("int->i32", "(subr pure (int) i32)"),
    ("i32->int", "(subr pure (i32) int)"),
    ("u32+", "(subr pure (u32 u32) u32)"),
    ("u32-", "(subr pure (u32 u32) u32)"),
    ("u32*", "(subr pure (u32 u32) u32)"),
    ("u32-quotient", "(subr pure (u32 u32) u32)"),
    ("u32-remainder", "(subr pure (u32 u32) u32)"),
    ("u32-and", "(subr pure (u32 u32) u32)"),
    ("u32-or", "(subr pure (u32 u32) u32)"),
    ("u32-xor", "(subr pure (u32 u32) u32)"),
    ("u32<", "(subr pure (u32 u32) (bool (then (< 0 1)) (else (<= 1 0))))"),
    ("u32<=", "(subr pure (u32 u32) (bool (then (<= 0 1)) (else (< 1 0))))"),
    ("u32>", "(subr pure (u32 u32) (bool (then (< 1 0)) (else (<= 0 1))))"),
    ("u32>=", "(subr pure (u32 u32) (bool (then (<= 1 0)) (else (< 0 1))))"),
    ("u32=", "(subr pure (u32 u32) (bool (then (= 0 1)) (else (not (= 0 1)))))"),
    ("u32-shl", "(subr pure (u32 int) u32)"),
    ("u32-shr", "(subr pure (u32 int) u32)"),
    ("u32-not", "(subr pure (u32) u32)"),
    ("int->u32", "(subr pure (int) u32)"),
    ("u32->int", "(subr pure (u32) int)"),
    ("i64+", "(subr pure (i64 i64) i64)"),
    ("i64-", "(subr pure (i64 i64) i64)"),
    ("i64*", "(subr pure (i64 i64) i64)"),
    ("i64-quotient", "(subr pure (i64 i64) i64)"),
    ("i64-remainder", "(subr pure (i64 i64) i64)"),
    ("i64-and", "(subr pure (i64 i64) i64)"),
    ("i64-or", "(subr pure (i64 i64) i64)"),
    ("i64-xor", "(subr pure (i64 i64) i64)"),
    ("i64<", "(subr pure (i64 i64) (bool (then (< 0 1)) (else (<= 1 0))))"),
    ("i64<=", "(subr pure (i64 i64) (bool (then (<= 0 1)) (else (< 1 0))))"),
    ("i64>", "(subr pure (i64 i64) (bool (then (< 1 0)) (else (<= 0 1))))"),
    ("i64>=", "(subr pure (i64 i64) (bool (then (<= 1 0)) (else (< 0 1))))"),
    ("i64=", "(subr pure (i64 i64) (bool (then (= 0 1)) (else (not (= 0 1)))))"),
    ("i64-shl", "(subr pure (i64 int) i64)"),
    ("i64-shr", "(subr pure (i64 int) i64)"),
    ("i64-not", "(subr pure (i64) i64)"),
    ("int->i64", "(subr pure (int) i64)"),
    ("i64->int", "(subr pure (i64) int)"),
    ("u64+", "(subr pure (u64 u64) u64)"),
    ("u64-", "(subr pure (u64 u64) u64)"),
    ("u64*", "(subr pure (u64 u64) u64)"),
    ("u64-quotient", "(subr pure (u64 u64) u64)"),
    ("u64-remainder", "(subr pure (u64 u64) u64)"),
    ("u64-and", "(subr pure (u64 u64) u64)"),
    ("u64-or", "(subr pure (u64 u64) u64)"),
    ("u64-xor", "(subr pure (u64 u64) u64)"),
    ("u64<", "(subr pure (u64 u64) (bool (then (< 0 1)) (else (<= 1 0))))"),
    ("u64<=", "(subr pure (u64 u64) (bool (then (<= 0 1)) (else (< 1 0))))"),
    ("u64>", "(subr pure (u64 u64) (bool (then (< 1 0)) (else (<= 0 1))))"),
    ("u64>=", "(subr pure (u64 u64) (bool (then (<= 1 0)) (else (< 0 1))))"),
    ("u64=", "(subr pure (u64 u64) (bool (then (= 0 1)) (else (not (= 0 1)))))"),
    ("u64-shl", "(subr pure (u64 int) u64)"),
    ("u64-shr", "(subr pure (u64 int) u64)"),
    ("u64-not", "(subr pure (u64) u64)"),
    ("int->u64", "(subr pure (int) u64)"),
    ("u64->int", "(subr pure (u64) int)"),
    // Variadic procedures (`vsubr`, `vlambda`): FX-87's.
    // `(list x …)`: a fresh list of its arguments, at any region, as a
    // `cons` chain may be; a `vsubr` as a value.
    ("list", "(poly ((t type) (r region)) (vsubr (alloc r) t (listof t r)))"),
    ("%vlambda", "(poly ((e effect) (t type) (r type)) (subr pure ((subr e ((listof t acyclic)) r)) (vsubr e t r)))"),
    ("apply", "(poly ((e effect) (t type) (r type) (g region)) (subr (maxeff e (read g)) ((vsubr e t r) (listof t g)) r))"),
    ("string-compare", "(subr pure (string string) int)"),
    ("string-search", "(subr pure (string string int) int)"),
    ("symbol-compare", "(subr pure (symbol symbol) int)"),
    ("string-ci=?", "(subr pure (string string) bool)"),
    ("string-downcase", "(subr pure (string) string)"),
    ("char->string", "(subr pure (char) string)"),
    ("list->string", "(poly ((r region)) (subr (read r) ((listof char r)) string))"),
    ("string->list", "(poly ((r region)) (subr (alloc r) (string) (listof char r)))"),
    // What the benchmark ports wrote for themselves (PLAN.md Q11).
    ("remainder", "(subr pure (int int) int)"),
    // Bits of an `int`, two's complement, a bignum's too (SRFI 151's
    // names): `arithmetic-shift` left by a positive count, right (floor)
    // by a negative one.
    ("bitwise-and", "(subr pure (int int) int)"),
    ("bitwise-ior", "(subr pure (int int) int)"),
    ("bitwise-xor", "(subr pure (int int) int)"),
    ("bitwise-not", "(subr pure (int) int)"),
    ("arithmetic-shift", "(subr pure (int int) int)"),
    ("zero?", "(subr pure (int) (bool (then (= 0 (lit 0))) (else (not (= 0 (lit 0))))))"),
    ("max", "(subr pure (int int) int)"),
    ("min", "(subr pure (int int) int)"),
    ("bool=?", "(subr pure (bool bool) bool)"),
    ("char<?", "(subr pure (char char) bool)"),
    ("char<=?", "(subr pure (char char) bool)"),
    ("char>?", "(subr pure (char char) bool)"),
    ("char>=?", "(subr pure (char char) bool)"),
    ("char-upcase", "(subr pure (char) char)"),
    ("string<?", "(subr pure (string string) bool)"),
    ("string<=?", "(subr pure (string string) bool)"),
    ("string>?", "(subr pure (string string) bool)"),
    ("string>=?", "(subr pure (string string) bool)"),
    // The run fails, saying why; it returns to no one.
    ("error", "(subr pure (string) void)"),
    ("append", "(poly ((r1 region) (r2 region)) (poly ((t type)) (subr (maxeff (read r1) (alloc r2)) ((listof t r1) (listof t r2)) (listof t r2))))"),
    // A list's length at any region; a cycle is an error.
    ("list-length", "(poly ((r region)) (poly ((t type)) (subr (read r) ((listof t r)) nat)))"),
    ("array->list", "(poly ((r1 region) (r2 region)) (poly ((t type)) (subr (maxeff (read r1) (alloc r2)) ((arrayof t r1)) (listof t r2))))"),
    ("list->array", "(poly ((r1 region) (r2 region)) (poly ((t type)) (subr (maxeff (read r1) (alloc r2)) ((listof t r1)) (arrayof t r2))))"),
    ("reverse", "(poly ((r1 region) (r2 region)) (poly ((t type)) (subr (maxeff (read r1) (alloc r2)) ((listof t r1)) (listof t r2))))"),
    ("parse-number", "(poly ((r region)) (subr (alloc r) (string int) (listof datum r)))"),
    ("parse-nat", "(subr pure (string int) int)"),
    ("datum-list", "(poly ((r region)) (subr (read r) ((listof datum r)) datum))"),
    ("datum-dotted", "(poly ((r region)) (subr (read r) ((listof datum r) datum) datum))"),
    ("datum-list->vector", "(subr pure (datum) datum)"),
    ("datum-list->bytevector", "(subr pure (datum) datum)"),
    ("datum-byte?", "(subr pure (datum) bool)"),
    ("datum-proper-list?", "(subr pure (datum) bool)"),
    // `(acyclic e (x body) else)` is these two: whether data has no cycle,
    // and, of a variable just found to have none, its value at `finite`
    // where it was `const` (`docs/research/confirmation.md`, CF0).
    // Each walks data at a place, so reads it: pure at the heap, where
    // reading frozen data is, and naming the place otherwise (F13).
    ("acyclic?", "(poly ((p place) (t data p)) (subr (read (const p)) (t) (bool (then (acyclic 0)) (else))))"),
    ("certify-acyclic", "(poly ((p place) (t data p)) (subr pure (t) t))"),
    // `(confirm-nat e (n body) else)` is these two: whether an integer is no
    // less than 0, and, where `nat?` has just said so of a variable, its
    // value as a `nat`.
    ("nat?", "(subr pure (int) (bool (then (nat 0)) (else)))"),
    ("certify-nat", "(subr pure (int) nat)"),
    // `(confirm-length e n (x body) else)` is these two: whether a frozen
    // list is proper and has `n` elements; and, of a variable just found
    // so, its value as a `(nlist T n)` (`docs/research/sizes.md`).
    ("length-is?", "(poly ((p place) (l data p)) (subr (read (const p)) (l int) (bool (then (length 0 1)) (else))))"),
    ("certify-length", "(poly ((p place) (l data p)) (subr pure (l int) l))"),
    // Whether a datum is a fixnum: an `int`, so it narrows to one.
    ("datum-int?", "(subr pure (datum) (bool (then (shape 0 int)) (else)))"),
    ("int->string", "(subr pure (int) string)"),
    ("string->symbol", "(subr pure (string) symbol)"),
    ("symbol->string", "(subr pure (symbol) string)"),
    ("symbol=?", "(subr pure (symbol symbol) bool)"),
    // A hash of a string's characters: the same string, the same hash.
    ("string-hash", "(subr pure (string) int)"),
    // A symbol's hash, kept with it when it was interned.
    ("symbol-name-hash", "(subr pure (symbol) int)"),
    // Arrays: bloblets whose fields are all one type, read by index.
    ("make-array", "(poly ((r region)) (poly ((t type)) (subr (alloc r) (int t) (arrayof t r))))"),
    ("array-ref", "(poly ((r region)) (poly ((t type)) (subr (read r) ((arrayof t r) int) t)))"),
    ("array-set!", "(poly ((r region)) (poly ((t type)) (subr (write r) ((arrayof t r) int t) unit)))"),
    ("array-length", "(poly ((r region)) (poly ((t type)) (subr pure ((arrayof t r)) nat)))"),
    // I-cells: written once, read after (docs/research/recursion-and-initialization.md).
    // A read waits for the write, so it is ordered after writes to the
    // region (`await`), but not after other reads.
    ("make-icell", "(poly ((r region)) (poly ((t type)) (subr (alloc r) () (icell t r))))"),
    ("icell-put!", "(poly ((r region)) (poly ((t type)) (subr (write r) ((icell t r) t) unit)))"),
    ("icell-get", "(poly ((r region)) (poly ((t type)) (subr (await r) ((icell t r)) t)))"),
    // Identity (PLAN.md Q5, `docs/fx26.md`, "Identity"): whether two values
    // are the same object. Exact on mutable objects, which no compiler
    // copies or merges; on immutable data and procedures, which compilers
    // may share, copy or rebuild, `#t` means the two are equal and `#f`
    // says nothing (OCaml's `==`, R6RS's `eqv?` on procedures).
    // Identical values are equal; equal ones (two bignums) may not be
    // identical, so the else branch proves nothing.
    ("eq?", "(poly ((t type)) (subr pure (t t) (bool (then (= 0 1)) (else))))"),
    // The kinds of key that have identity, and tables keyed by it, hashed
    // by address. A table's key kind is a mutable object's, and its
    // operations write the keys' region, so that no table is keyed by
    // frozen data, whose lookups would depend on what the compilers shared.
    ("pair-identity", "(poly ((r region)) (poly ((t1 type) (t2 type)) (subr pure () (identity (pairof t1 t2 r) r))))"),
    ("ref-identity", "(poly ((r region)) (poly ((t type)) (subr pure () (identity (ref t r) r))))"),
    ("array-identity", "(poly ((r region)) (poly ((t type)) (subr pure () (identity (arrayof t r) r))))"),
    ("icell-identity", "(poly ((r region)) (poly ((t type)) (subr pure () (identity (icell t r) r))))"),
    ("make-eqtable", "(poly ((kr region) (r region)) (poly ((k type) (v type)) (subr (alloc r) ((identity k kr)) (eqtable k v kr r))))"),
    ("eqtable-ref", "(poly ((kr region) (r region)) (poly ((k type) (v type)) (subr (maxeff (read r) (write kr)) ((eqtable k v kr r) k v) v)))"),
    ("eqtable-has?", "(poly ((kr region) (r region)) (poly ((k type) (v type)) (subr (maxeff (read r) (write kr)) ((eqtable k v kr r) k) bool)))"),
    ("eqtable-count", "(poly ((kr region) (r region)) (poly ((k type) (v type)) (subr (read r) ((eqtable k v kr r)) int)))"),
    (
        "eqtable-set!",
        "(poly ((kr region) (r region)) (poly ((k type) (v type)) (subr (maxeff (write r) (alloc r) (write kr)) ((eqtable k v kr r) k v) unit)))",
    ),
    ("eqtable-delete!", "(poly ((kr region) (r region)) (poly ((k type) (v type)) (subr (maxeff (write r) (write kr)) ((eqtable k v kr r) k) unit)))"),
    // Cellular code (`layout::cellular`), for the compiler written in
    // FX-26. A word is immutable once made, so making one is pure; a word
    // that is not one (`Heap::make_cellular_word`) is an error when run.
    ("make-word", "(poly ((r region)) (subr (read r) (symbol (listof wcell r)) tword))"),
    // A word's register code (PLAN.md 13h′) made from its cells, checked,
    // and set as the word's twin; it is given back.
    ("set-register-twin", "(poly ((r region)) (subr (read r) (tword (listof wcell r)) tword))"),
    // A word's cells, looked at, for the compiler to machine code: how many
    // fields it has, and field k if it is an int.
    ("tword-fields", "(subr pure (tword) int)"),
    // Any value's cellular code, shown, if it has some: for looking at what
    // the compiler made.
    ("disassemble", "(poly ((t type)) (subr pure (t) string))"),
    ("tword-int?", "(subr pure (tword int) bool)"),
    ("tword-int", "(subr pure (tword int) int)"),
    ("wcell-routine", "(subr pure (int) wcell)"),
    ("wcell-int", "(subr pure (int) wcell)"),
    ("wcell-bool", "(subr pure (bool) wcell)"),
    ("wcell-string", "(subr pure (string) wcell)"),
    ("wcell-char", "(subr pure (char) wcell)"),
    ("wcell-f64", "(subr pure (f64) wcell)"),
    ("wcell-symbol", "(subr pure (symbol) wcell)"),
    ("wcell-unit", "(subr pure () wcell)"),
    ("wcell-word", "(subr pure (tword) wcell)"),
    ("wcell-global", "(subr pure (wglobal) wcell)"),
    ("wcell-self", "(subr pure () wcell)"),
    ("wcell-nil", "(subr pure () wcell)"),
    ("wcell-sum", "(subr pure (symbol wcell) wcell)"),
    // A pair of constants, made while compiling: a constant list's
    // (`TODO.md` §44).
    ("wcell-pair", "(subr pure (wcell wcell) wcell)"),
    // A constant datum, interned (`Heap::intern_datum`): a quote's.
    ("wcell-interned", "(subr pure (wcell) wcell)"),
    // A lambda-lifted procedure's closure, over nothing, its word to come;
    // and its word, once compiled.
    ("wcell-closure", "(subr pure () wcell)"),
    ("close-over-word!", "(subr pure (wcell tword) unit)"),
    ("wcell-product", "(poly ((r region)) (subr (read r) ((listof wcell r)) wcell))"),
    // A global's cell, new: its value is the compiled program's to change.
    ("make-global", "(subr pure (symbol) wglobal)"),
    // How many times a global has been written: what the compiler's guards
    // test it against (`layout::cellular::GLOBAL_WRITES`). Only a program
    // compiled changes it, as it runs, after it is compiled; so, to the
    // compiler, the same each time it asks.
    ("wglobal-writes", "(subr pure (wglobal) int)"),
    // A global's name, as it was made (`make-global`).
    ("wglobal-name", "(subr pure (wglobal) symbol)"),
    // Whether two globals are the one.
    ("wglobal=?", "(subr pure (wglobal wglobal) bool)"),
    // A runtime primitive's number, for `prim`, or -1.
    ("runtime-primitive", "(subr pure (string) int)"),
    ("runtime-primitive-arity", "(subr pure (string) int)"),
    (
        "make-continuation-prompt-tag",
        "(poly ((r region)) (poly ((a type) (h type) (d effect))
           (subr (alloc r) () (prompt-tag a h d r))))",
    ),
    (
        "abort-current-continuation",
        "(poly ((r region)) (poly ((a type) (h type) (d effect))
           (subr (goto r) ((prompt-tag a h d r) h) void)))",
    ),
    (
        "call-with-composable-continuation",
        "(poly ((r region)) (poly ((a type) (h type) (d effect) (t type) (e effect))
           (subr (maxeff (comefrom r) e)
                 ((subr e ((composable t a d r)) t) (prompt-tag a h d r))
                 t)))",
    ),
    ("make-continuation-mark-key", "(poly ((r region)) (poly ((t type)) (subr (alloc r) () (mark-key t r))))"),
    (
        "with-mark",
        "(poly ((r region)) (poly ((t type) (a type) (e effect))
           (subr (maxeff (write r) e) ((mark-key t r) t (subr e () a)) a)))",
    ),
    ("first-mark", "(poly ((r region)) (poly ((t type)) (subr (read r) ((mark-key t r) t) t)))"),
    (
        "current-marks",
        "(poly ((r region) (l region)) (poly ((t type))
           (subr (maxeff (read r) (alloc l)) ((mark-key t r)) (listof t l))))",
    ),
    (
        "marks-of",
        "(poly ((q region) (r region) (l region)) (poly ((v type) (t type) (a type) (d effect))
           (subr (maxeff (read q) (alloc l)) ((composable t a d r) (mark-key v q)) (listof v l))))",
    ),
];

/// The initial environment as text, for the checker written in FX-26:
/// the standard generative types' declarations (`check::VSUBR`,
/// `FLATLAYOUT`, `FLATARRAYOF`, `IDENTITY`, `EQTABLE`: 0 to 4), `datum`'s
/// (`check::DATUM`), then `(name type)` for each binding.
pub fn standard_text() -> String {
    let decl: String = [
        crate::check::VSUBR,
        crate::check::FLATLAYOUT,
        crate::check::FLATARRAYOF,
        crate::check::IDENTITY,
        crate::check::EQTABLE,
    ]
        .iter()
        .map(|d| format!("(define-generative {d})\n"))
        .collect::<String>()
        + &format!("(define-type datum {})\n", crate::check::DATUM);
    decl + &ENTRIES.iter().map(|(n, t)| format!("({n} {t})\n")).collect::<String>()
}
