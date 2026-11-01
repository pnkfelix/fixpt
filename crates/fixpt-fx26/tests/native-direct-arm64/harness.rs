//! What the tests of the native convention's compiler to arm64 written in
//! FX-26 share, piece by piece (`tests/native_direct_arm64*.rs`): a program
//! of the modules, the names it uses of them and each piece's wrapper; and
//! each case run by FX-26 and by the Rust piece of the same name
//! (`fixpt_native::direct::oracle_arm64`, its `harness`), the same bytes and
//! call-outs, or the same refusal.
//!
//! A wrapper resets the assembler (its call-outs numbered after the
//! machine's own, `OWN_CALLOUTS`), makes the labels its piece is given,
//! runs it, and ends with `t-out` (`out.fx`): the labels bound in order, a
//! `brk #0`, the traps' stubs placed, each call-out's load given field
//! `n + 3`, and its count of call-outs, the call-outs, what it answered
//! (`pre`), and its bytes, or 0xee if it could not, `ada-err` saying why.

#![allow(dead_code)]

use fixpt_engine::Backend;
use fixpt_heap::Value;

/// An argument to a piece: FX-26 is given it as itself, the Rust oracle
/// as integers (a flag 0 or 1; a name as its bytes, last; a list, its
/// items).
#[derive(Clone, Debug)]
pub enum A {
    I(i64),
    B(bool),
    S(&'static str),
    L(Vec<i64>),
}

pub const EFF: &str = "(maxeff (read @globals) (read @k) (write @k) (alloc @k) spin)";

/// A piece's FX-26 wrapper: its name (`t-name` calls it), its parameters'
/// names and types, how many labels it is given (`l0`, `l1`, …), and the
/// call.
pub type Wrapper = (&'static str, &'static [(&'static str, &'static str)], usize, &'static str);

/// The program: `modules` (which define `arm64`, `dl` and `asm` at least),
/// each of `names` defined at top level from its module (`(name module)`),
/// `out.fx`, then `extra` (what the wrappers use, and wrappers of their own
/// shapes), then the wrappers, each `t-` and its piece's name.
pub fn program(modules: &str, names: &[(&str, &str)], wrappers: &[Wrapper], extra: &str) -> String {
    let mut p = String::from(modules);
    for n in [
        "ada-reset", "ada-label", "ada-bind", "ada-e", "ada-place-stubs", "ada-finish", "ada-callouts", "ada-callout-loads-made", "ada-callout-field", "ada-ok?",
        "ada-err", "ada-co",
    ] {
        p.push_str(&format!("(define {n} (with asm {n}))\n"));
    }
    for (n, m) in names {
        p.push_str(&format!("(define {n} (with {m} {n}))\n"));
    }
    p.push_str(&include_str!("out.fx").replace("{EFF}", EFF));
    p.push_str(&extra.replace("{EFF}", EFF));
    let labels = |n: usize| (0..n).map(|k| format!("(l{k} (ada-label))")).collect::<Vec<_>>().join(" ");
    let list = |n: usize| (0..n).rev().fold("nil".to_string(), |acc, k| format!("(cons l{k} {acc})"));
    for (name, params, n, call) in wrappers {
        let types = params.iter().map(|p| p.1).collect::<Vec<_>>().join(" ");
        let names = params.iter().map(|p| p.0).collect::<Vec<_>>().join(" ");
        p.push_str(&format!(
            "(define t-{name} (subr {EFF} ({types}) (listof int @k))\n  \
               (lambda ({names}) (begin (ada-reset 10) (let* ({ls}) (begin {call} (t-out nil {l}))))))\n",
            ls = if *n == 0 { "(l- 0)".to_string() } else { labels(*n) },
            l = list(*n),
        ));
    }
    p
}

/// The program checked and loaded into a session of its own.
pub fn session(program: &str) -> fixpt_scheme::Session {
    let compiled = fixpt_fx26::session::compile_program(program).unwrap_or_else(|e| panic!("checks: {e}\n{program}"));
    let mut s = fixpt_scheme::Session::with_backend(Backend::Bytecode);
    compiled.load_into(&mut s).expect("loads");
    s
}

/// The Rust oracle's integers for `args`.
pub fn ints(args: &[A]) -> Vec<i64> {
    let mut out = Vec::new();
    for a in args {
        match *a {
            A::I(n) => out.push(n),
            A::B(b) => out.push(b as i64),
            A::S(s) => out.extend(s.bytes().map(i64::from)),
            A::L(ref l) => out.extend(l),
        }
    }
    out
}

/// What a case is: the piece's name, FX-26's arguments, and Rust's.
pub type Case = (&'static str, Vec<A>, Vec<i64>);

/// Each case run by both: what differs, after saying how many of each
/// were compared.
pub fn compare(s: &mut fixpt_scheme::Session, cases: &[Case]) -> Vec<String> {
    let mut wrong = Vec::new();
    let mut per: std::collections::BTreeMap<&str, usize> = Default::default();
    for (name, fx, rust) in cases {
        *per.entry(name).or_default() += 1;
        if std::env::var_os("FIXPT_TRACE_PIECES").is_some() { eprintln!("{name} {fx:?}"); }
        let (want_code, want_calls) = fixpt_native::direct::oracle_arm64(name, rust).unwrap_or_else(|| panic!("no Rust piece {name}"));
        let got: Vec<i64> = s.scope(|sc| {
            let args: Vec<_> = fx
                .iter()
                .map(|a| match *a {
                    A::I(n) => sc.make(|_| Value::fixnum(n)),
                    A::B(b) => sc.make(|_| Value::boolean(b)),
                    A::S(t) => sc.make(|m| m.heap().make_string(t)),
                    A::L(ref l) => sc.make(|m| l.iter().rev().fold(Value::NULL, |acc, &n| m.heap().cons(Value::fixnum(n), acc))),
                })
                .collect();
            let r = sc.call_global(&format!("fx:t-{name}"), &args).unwrap_or_else(|e| panic!("{name} {fx:?} runs: {e}"));
            sc.view(|v| v.get(r).list().expect("a list").iter().map(|b| b.fixnum().expect("an int")).collect())
        });
        let k = got[0] as usize;
        let (calls, mut code): (Vec<i64>, Vec<u8>) = (got[1..1 + k].to_vec(), got[1 + k..].iter().map(|&b| b as u8).collect());
        if code.last() == Some(&0xee) && want_code.contains(&0xee) {
            let why = s.scope(|sc| {
                let r = sc.call_global("fx:ada-err", &[]).expect("runs");
                sc.view(|v| v.get(r).string().unwrap_or_default())
            });
            code.extend(why.bytes());
        }
        if code != want_code || calls != want_calls {
            wrong.push(format!("{name} {fx:?}: FX-26 {code:02x?} {calls:?}, Rust {want_code:02x?} {want_calls:?}"));
        }
    }
    eprintln!("{} pieces compared: {per:?}; {} differ", cases.len(), wrong.len());
    wrong
}
