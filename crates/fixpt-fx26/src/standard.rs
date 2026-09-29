//! The initial environment.
//!
//! The memory operations have FX-87's types, from its standard environment
//! (`crates/fixpt-fx87/src/standard.fx`), less the trailing `@=` that FX-87
//! uses for the region of a variable's own binding, which the kernel does not
//! have. `cwcc` has the type PLDI '89 gives it (p. 4), binders written in
//! FX-87's parenthesised style.
//!
//! Lists are FX-87's: `(listof t r)` is a pair whose tail is the list again,
//! and every pair type also has `nil`, which `null?` tests for.
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
    ("car", "(poly ((r region)) (poly ((t1 type) (t2 type)) (subr (read r) ((pairof t1 t2 r)) t1)))"),
    ("cdr", "(poly ((r region)) (poly ((t1 type) (t2 type)) (subr (read r) ((pairof t1 t2 r)) t2)))"),
    // The identity, which the native convention's compiler declines: a
    // procedure calling it runs as cellular code.
    ("stay-cellular", "(poly ((t type)) (subr pure (t) t))"),
    ("set-car!", "(poly ((r region)) (poly ((t1 type) (t2 type)) (subr (write r) ((pairof t1 t2 r) t1) unit)))"),
    ("set-cdr!", "(poly ((r region)) (poly ((t1 type) (t2 type)) (subr (write r) ((pairof t1 t2 r) t2) unit)))"),
    ("nil", "(poly ((r region)) (poly ((t1 type) (t2 type)) (pairof t1 t2 r)))"),
    ("null?", "(poly ((r region)) (poly ((t1 type) (t2 type)) (subr pure ((pairof t1 t2 r)) bool)))"),
    ("+", "(subr pure (int int) int)"),
    ("-", "(subr pure (int int) int)"),
    // A finite list's length, as a natural of its size.
    ("length", "(poly ((t type) (n size)) (subr pure ((nlist t n)) (nat n)))"),
    ("=", "(subr pure (int int) bool)"),
    (
        "cwcc",
        "(poly ((r region)) (poly ((t type)) (poly ((e effect))
           (subr (maxeff (comefrom r) e)
                 ((subr e ((subr (goto r) (t) void)) t))
                 t))))",
    ),
    ("<", "(subr pure (int int) bool)"),
    (">", "(subr pure (int int) bool)"),
    ("<=", "(subr pure (int int) bool)"),
    (">=", "(subr pure (int int) bool)"),
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
    // The fixed-width integers (PLAN.md, Q2 b): wrapping arithmetic.
    ("i32+", "(subr pure (i32 i32) i32)"),
    ("i32-", "(subr pure (i32 i32) i32)"),
    ("i32*", "(subr pure (i32 i32) i32)"),
    ("i32-quotient", "(subr pure (i32 i32) i32)"),
    ("i32-remainder", "(subr pure (i32 i32) i32)"),
    ("i32-and", "(subr pure (i32 i32) i32)"),
    ("i32-or", "(subr pure (i32 i32) i32)"),
    ("i32-xor", "(subr pure (i32 i32) i32)"),
    ("i32<", "(subr pure (i32 i32) bool)"),
    ("i32<=", "(subr pure (i32 i32) bool)"),
    ("i32>", "(subr pure (i32 i32) bool)"),
    ("i32>=", "(subr pure (i32 i32) bool)"),
    ("i32=", "(subr pure (i32 i32) bool)"),
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
    ("u32<", "(subr pure (u32 u32) bool)"),
    ("u32<=", "(subr pure (u32 u32) bool)"),
    ("u32>", "(subr pure (u32 u32) bool)"),
    ("u32>=", "(subr pure (u32 u32) bool)"),
    ("u32=", "(subr pure (u32 u32) bool)"),
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
    ("i64<", "(subr pure (i64 i64) bool)"),
    ("i64<=", "(subr pure (i64 i64) bool)"),
    ("i64>", "(subr pure (i64 i64) bool)"),
    ("i64>=", "(subr pure (i64 i64) bool)"),
    ("i64=", "(subr pure (i64 i64) bool)"),
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
    ("u64<", "(subr pure (u64 u64) bool)"),
    ("u64<=", "(subr pure (u64 u64) bool)"),
    ("u64>", "(subr pure (u64 u64) bool)"),
    ("u64>=", "(subr pure (u64 u64) bool)"),
    ("u64=", "(subr pure (u64 u64) bool)"),
    ("u64-shl", "(subr pure (u64 int) u64)"),
    ("u64-shr", "(subr pure (u64 int) u64)"),
    ("u64-not", "(subr pure (u64) u64)"),
    ("int->u64", "(subr pure (int) u64)"),
    ("u64->int", "(subr pure (u64) int)"),
    ("string-compare", "(subr pure (string string) int)"),
    ("string-search", "(subr pure (string string int) int)"),
    ("symbol-compare", "(subr pure (symbol symbol) int)"),
    ("string-ci=?", "(subr pure (string string) bool)"),
    ("string-downcase", "(subr pure (string) string)"),
    ("char->string", "(subr pure (char) string)"),
    ("list->string", "(poly ((r region)) (subr (read r) ((listof char r)) string))"),
    ("string->list", "(poly ((r region)) (subr (alloc r) (string) (listof char r)))"),
    ("reverse", "(poly ((r1 region) (r2 region)) (poly ((t type)) (subr (maxeff (read r1) (alloc r2)) ((listof t r1)) (listof t r2))))"),
    ("parse-number", "(poly ((r region)) (subr (alloc r) (string int) (listof datum r)))"),
    ("parse-nat", "(subr pure (string int) int)"),
    ("datum-char", "(subr pure (char) datum)"),
    ("datum-string", "(subr pure (string) datum)"),
    ("datum-symbol", "(subr pure (string) datum)"),
    ("datum-bool", "(subr pure (bool) datum)"),
    ("datum-int", "(subr pure (int) datum)"),
    ("datum-list", "(poly ((r region)) (subr (read r) ((listof datum r)) datum))"),
    // A datum pair, made new: a list datum grown a pair at a time.
    ("datum-cons", "(subr pure (datum datum) datum)"),
    ("datum-dotted", "(poly ((r region)) (subr (read r) ((listof datum r) datum) datum))"),
    ("datum-list->vector", "(subr pure (datum) datum)"),
    ("datum-list->bytevector", "(subr pure (datum) datum)"),
    ("datum-char-value", "(subr pure (datum) char)"),
    ("datum-byte?", "(subr pure (datum) bool)"),
    ("datum-proper-list?", "(subr pure (datum) bool)"),
    // `(acyclic e (x body) else)` is these two: whether data has no cycle,
    // and, of a variable just found to have none, its value at `finite`
    // where it was `const` (`docs/research/confirmation.md`, CF0).
    ("acyclic?", "(poly ((t data)) (subr pure (t) bool))"),
    ("certify-acyclic", "(poly ((t data)) (subr pure (t) t))"),
    // `(confirm-nat e (n body) else)` is these two: whether an integer is no
    // less than 0, and, where `nat?` has just said so of a variable, its
    // value as a `nat`.
    ("nat?", "(subr pure (int) bool)"),
    ("certify-nat", "(subr pure (int) nat)"),
    // `(confirm-length e n (x body) else)` is these two: whether a frozen
    // list is proper and has `n` elements; and, of a variable just found
    // so, its value as a `(nlist T n)` (`docs/research/sizes.md`).
    ("length-is?", "(poly ((l data)) (subr pure (l int) bool))"),
    ("certify-length", "(poly ((l data)) (subr pure (l int) l))"),
    ("datum-pair?", "(subr pure (datum) bool)"),
    ("datum-null?", "(subr pure (datum) bool)"),
    ("datum-car", "(subr pure (datum) datum)"),
    ("datum-cdr", "(subr pure (datum) datum)"),
    ("datum-symbol?", "(subr pure (datum) bool)"),
    ("datum-symbol-name", "(subr pure (datum) string)"),
    ("datum-int?", "(subr pure (datum) bool)"),
    ("datum-int-value", "(subr pure (datum) int)"),
    ("datum-string?", "(subr pure (datum) bool)"),
    ("datum-string-value", "(subr pure (datum) string)"),
    ("datum-bool?", "(subr pure (datum) bool)"),
    ("datum-bool-value", "(subr pure (datum) bool)"),
    ("datum-char?", "(subr pure (datum) bool)"),
    ("datum->symbol", "(subr pure (datum) symbol)"),
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
    ("wcell-symbol", "(subr pure (symbol) wcell)"),
    ("wcell-unit", "(subr pure () wcell)"),
    ("wcell-word", "(subr pure (tword) wcell)"),
    ("wcell-global", "(subr pure (wglobal) wcell)"),
    ("wcell-self", "(subr pure () wcell)"),
    ("wcell-nil", "(subr pure () wcell)"),
    ("wcell-sum", "(subr pure (symbol wcell) wcell)"),
    // A lambda-lifted procedure's closure, over nothing, its word to come;
    // and its word, once compiled.
    ("wcell-closure", "(subr pure () wcell)"),
    ("close-over-word!", "(subr pure (wcell tword) unit)"),
    ("wcell-product", "(poly ((r region)) (subr (read r) ((listof wcell r)) wcell))"),
    // A global's cell, new: its value is the compiled program's to change.
    ("make-global", "(subr pure (symbol) wglobal)"),
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
