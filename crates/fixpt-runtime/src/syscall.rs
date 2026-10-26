//! The syscalls this runtime provides (`docs/research/syscalls.md`): each a
//! capability a program declares by name with `define-syscall` or
//! `define-optional-syscall`, at a type both sides state. A program's
//! declaration and an entry here are compared as text, each type in its
//! canonical form (`docs/fx26.md`, "Syscalls"), so this table keeps each
//! type written out, as the checkers print it (a test in `fixpt-fx26` says
//! they agree).

use crate::error::Outcome;
use crate::runtime::Runtime;
use fixpt_heap::Value;

/// One syscall: its host name (`namespace:name/version`), its type in
/// canonical form, and what it does, given its arguments.
pub struct Syscall {
    pub host: &'static str,
    pub canonical: &'static str,
    pub run: fn(&mut Runtime, &[Value]) -> Outcome<Value>,
}

/// The most arguments a syscall takes.
pub const MAX_ARGS: usize = 6;

/// The syscalls this runtime has.
pub const SYSCALLS: &[Syscall] = &[
    // An executable view of a flat array's range. Fixpt's flat arrays move
    // when collected, so it never keeps one at an address that does not
    // change: the view fails, -1, as the note allows.
    Syscall {
        host: "code:exec-view/1",
        canonical: "(poly ((r1 region)) (subr (maxeff (io sys) (write r1)) ((flatarrayof i64 r1) int int) int))",
        run: |_rt, _a| Ok(Value::fixnum(-1)),
    },
    Syscall { host: "code:page-words/1", canonical: "(subr (io sys) () int)", run: |_rt, _a| Ok(Value::fixnum(page_words())) },
    // The instruction cache made to see a view's words as written: no view
    // is ever made here, so there is nothing to flush.
    Syscall {
        host: "code:flush/1",
        canonical: "(poly ((r1 region)) (subr (maxeff (io sys) (read r1)) ((flatarrayof i64 r1) int int) unit))",
        run: |_rt, _a| Ok(Value::UNIT),
    },
];

/// The words in one page of this machine.
fn page_words() -> i64 {
    (fixpt_memmgmt::reserve::probe::page() / 8) as i64
}

/// What this runtime has under `host`: the syscall, if its type is
/// `canonical`; else its own type, if it has the name at another.
fn find(host: &str, canonical: &str) -> Result<&'static Syscall, Option<&'static str>> {
    match SYSCALLS.iter().find(|s| s.host == host) {
        Some(s) if s.canonical == canonical => Ok(s),
        Some(s) => Err(Some(s.canonical)),
        None => Err(None),
    }
}

/// A required syscall's check, as its declaration runs: `label` is how its
/// messages name it, `syscall NAME ("HOST")`.
pub fn require(rt: &mut Runtime, label: &str, host: &str, canonical: &str) -> Outcome<Value> {
    match find(host, canonical) {
        Ok(_) => Ok(Value::UNIT),
        Err(None) => rt.fail(&format!("{label}: this runtime has none"), &[]),
        Err(Some(theirs)) => rt.fail(&format!("{label}: declared {canonical}; this runtime's is {theirs}"), &[]),
    }
}

/// Whether this runtime has `host` at the type `canonical`.
pub fn available(host: &str, canonical: &str) -> bool {
    find(host, canonical).is_ok()
}

/// A call of a syscall, with its arguments.
pub fn call(rt: &mut Runtime, label: &str, host: &str, canonical: &str, args: &[Value]) -> Outcome<Value> {
    match find(host, canonical) {
        Ok(s) => (s.run)(rt, args),
        Err(_) => rt.fail(&format!("{label}: not available on this runtime"), &[]),
    }
}
