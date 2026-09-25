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
