//! The initial environment.
//!
//! The memory operations have FX-87's types, from its standard environment
//! (`crates/fixpt-fx87/src/standard.fx`), less the trailing `@=` that FX-87
//! uses for the region of a variable's own binding, which the kernel does not
//! have. `cwcc` has the type PLDI '89 gives it (p. 4), binders written in
//! FX-87's parenthesised style.

pub const ENTRIES: &[(&str, &str)] = &[
    ("new", "(poly ((r region)) (poly ((t type)) (subr (alloc r) (t) (ref t r))))"),
    ("get", "(poly ((r region)) (poly ((t type)) (subr (read r) ((ref t r)) t)))"),
    ("set", "(poly ((r region)) (poly ((t type)) (subr (write r) ((ref t r) t) unit)))"),
    ("cons", "(poly ((r region)) (poly ((t1 type) (t2 type)) (subr (alloc r) (t1 t2) (pairof t1 t2 r))))"),
    ("car", "(poly ((r region)) (poly ((t1 type) (t2 type)) (subr (read r) ((pairof t1 t2 r)) t1)))"),
    ("cdr", "(poly ((r region)) (poly ((t1 type) (t2 type)) (subr (read r) ((pairof t1 t2 r)) t2)))"),
    ("set-car!", "(poly ((r region)) (poly ((t1 type) (t2 type)) (subr (write r) ((pairof t1 t2 r) t1) unit)))"),
    ("set-cdr!", "(poly ((r region)) (poly ((t1 type) (t2 type)) (subr (write r) ((pairof t1 t2 r) t2) unit)))"),
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
];
