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
    ("car", "(poly ((r region)) (poly ((t1 type) (t2 type)) (subr (read r) ((pairof t1 t2 r)) t1)))"),
    ("cdr", "(poly ((r region)) (poly ((t1 type) (t2 type)) (subr (read r) ((pairof t1 t2 r)) t2)))"),
    ("set-car!", "(poly ((r region)) (poly ((t1 type) (t2 type)) (subr (write r) ((pairof t1 t2 r) t1) unit)))"),
    ("set-cdr!", "(poly ((r region)) (poly ((t1 type) (t2 type)) (subr (write r) ((pairof t1 t2 r) t2) unit)))"),
    ("nil", "(poly ((r region)) (poly ((t1 type) (t2 type)) (pairof t1 t2 r)))"),
    ("null?", "(poly ((r region)) (poly ((t1 type) (t2 type)) (subr pure ((pairof t1 t2 r)) bool)))"),
    ("+", "(subr pure (int int) int)"),
    ("-", "(subr pure (int int) int)"),
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
    ("string-length", "(subr pure (string) int)"),
    ("string-ref", "(subr pure (string int) char)"),
    ("substring", "(subr pure (string int int) string)"),
    ("string=?", "(subr pure (string string) bool)"),
    ("string-ci=?", "(subr pure (string string) bool)"),
    ("string-downcase", "(subr pure (string) string)"),
    ("char->string", "(subr pure (char) string)"),
    ("list->string", "(poly ((r region)) (subr (read r) ((listof char r)) string))"),
    ("string->list", "(poly ((r region)) (subr (alloc r) (string) (listof char r)))"),
    ("reverse", "(poly ((r1 region) (r2 region)) (poly ((t type)) (subr (maxeff (read r1) (alloc r2)) ((listof t r1)) (listof t r2))))"),
    ("parse-number", "(poly ((r region)) (subr (alloc r) (string int) (listof datum r)))"),
    ("parse-int", "(subr pure (string int) int)"),
    ("datum-char", "(subr pure (char) datum)"),
    ("datum-string", "(subr pure (string) datum)"),
    ("datum-symbol", "(subr pure (string) datum)"),
    ("datum-bool", "(subr pure (bool) datum)"),
    ("datum-int", "(subr pure (int) datum)"),
    ("datum-list", "(poly ((r region)) (subr (read r) ((listof datum r)) datum))"),
    ("datum-dotted", "(poly ((r region)) (subr (read r) ((listof datum r) datum) datum))"),
    ("datum-list->vector", "(subr pure (datum) datum)"),
    ("datum-list->bytevector", "(subr pure (datum) datum)"),
    ("datum-char-value", "(subr pure (datum) char)"),
    ("datum-byte?", "(subr pure (datum) bool)"),
    ("datum-proper-list?", "(subr pure (datum) bool)"),
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
    // Arrays: bloblets whose fields are all one type, read by index.
    ("make-array", "(poly ((r region)) (poly ((t type)) (subr (alloc r) (int t) (arrayof t r))))"),
    ("array-ref", "(poly ((r region)) (poly ((t type)) (subr (read r) ((arrayof t r) int) t)))"),
    ("array-set!", "(poly ((r region)) (poly ((t type)) (subr (write r) ((arrayof t r) int t) unit)))"),
    ("array-length", "(poly ((r region)) (poly ((t type)) (subr pure ((arrayof t r)) int)))"),
    // Threaded code (`layout::threaded`), for the compiler written in
    // FX-26. A word is immutable once made, so making one is pure; a word
    // that is not one (`Heap::make_threaded_word`) is an error when run.
    ("make-word", "(poly ((r region)) (subr (read r) (symbol (listof wcell r)) tword))"),
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
    // A global's cell, new: its value is the compiled program's to change.
    ("make-global", "(subr pure (symbol) wglobal)"),
    // A runtime primitive's number, for `prim`, or -1.
    ("runtime-primitive", "(subr pure (string) int)"),
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
