//! A phase-1 namespace (`phase1.rs`; `docs/research/typed-macros.md`,
//! "Decided: transformers in the front end's heap", stage 3): made in a
//! session's runtime, a transformer defined in it and called on a datum
//! there, its answer a value of that heap; two namespaces apart.

use fixpt_fx26::session::Fx26Session;
use fixpt_read::FileId;

const SC: &str = "(subr spin (datum symbol) datum)";

fn session() -> Fx26Session {
    Fx26Session::with_backend(fixpt_engine::Backend::Bytecode).expect("a session")
}

/// `(NAME 5)`, as a reader makes it, in `rt`'s heap.
fn use_of(rt: &mut fixpt_runtime::Runtime, name: &str) -> fixpt_heap::Value {
    let head = rt.heap.intern(name);
    let base = rt.heap.push_root(head);
    let tail = rt.heap.cons(fixpt_heap::Value::fixnum(5), fixpt_heap::Value::NULL);
    let head = rt.heap.root_at(base);
    rt.heap.pop_roots_to(base);
    rt.heap.cons(head, tail)
}

#[test]
fn a_transformer_defined_in_phase_1_is_called_on_a_datum_of_the_heap() {
    let mut s = session();
    let p = s.phase1().unwrap_or_else(|e| panic!("phase 1: {e}"));
    let rt = s.scheme.runtime_unrooted();
    p.define(rt, "inc", SC, "(lambda (form env) `(+ ,(car (cdr form)) 1))").unwrap_or_else(|e| panic!("defined: {e}"));
    let form = use_of(rt, "inc");
    let env = rt.heap.intern("%env:use");
    let out = p.call(rt, "inc", &[form, env]).unwrap_or_else(|e| panic!("called: {e}"));
    assert_eq!(fixpt_runtime::write_value(&rt.heap, out), "(+ 5 1)");
    // The prelude's procedures are there for a transformer to use: bound
    // around its `lambda`, as `procedural::helpers` binds them, read where it
    // is defined, so that its type reads no global.
    let closes = "(let ((make-syntactic-closure %make-syntactic-closure))\n\
                  (lambda (form env) (make-syntactic-closure env '() (car (cdr form)))))";
    p.define(rt, "closes", SC, closes).unwrap_or_else(|e| panic!("defined: {e}"));
    let form = use_of(rt, "closes");
    let env = rt.heap.intern("%env:use");
    let out = p.call(rt, "closes", &[form, env]).unwrap_or_else(|e| panic!("called: {e}"));
    assert!(fixpt_runtime::write_value(&rt.heap, out).starts_with("(%sc "), "a syntactic closure");
    p.end(rt);
}

#[test]
fn a_definition_phase_1_refuses_says_why() {
    let mut s = session();
    let p = s.phase1().unwrap_or_else(|e| panic!("phase 1: {e}"));
    let rt = s.scheme.runtime_unrooted();
    let e = p.define(rt, "bad", SC, "(lambda (form env) (+ form 1))").expect_err("ill-typed");
    assert!(!e.is_empty(), "a message");
    // Naming a global reads it, as in a program: not of a `spin` type.
    let e = p.define(rt, "reads", SC, "(lambda (form env) (%make-syntactic-closure env '() form))").expect_err("reads a global");
    assert!(e.contains("(read (globals %make-syntactic-closure))"), "{e}");
    p.end(rt);
}

#[test]
fn two_namespaces_are_apart() {
    let mut s = session();
    let one = s.phase1().unwrap_or_else(|e| panic!("phase 1: {e}"));
    let two = s.phase1().unwrap_or_else(|e| panic!("phase 1: {e}"));
    let rt = s.scheme.runtime_unrooted();
    one.define(rt, "only-here", SC, "(lambda (form env) form)").unwrap_or_else(|e| panic!("defined: {e}"));
    assert!(one.value(rt, "only-here").is_some());
    assert!(two.value(rt, "only-here").is_none(), "another namespace's definition");
    // Nor is phase 0's: the program's globals are not phase 1's.
    s.run_program("(define phase-zero int 1)").expect("runs").expect("checks");
    let rt = s.scheme.runtime_unrooted();
    assert!(two.value(rt, "phase-zero").is_none(), "the program's global");
    one.end(rt);
    two.end(rt);
}

/// Each program read, then each of its forms run (as `fixpt run` and the
/// REPL's entries are), is an expansion of its own: its transformers called
/// in a namespace made for it, and none for one with no transformer's call.
#[test]
fn each_entry_has_a_namespace_of_its_own() {
    let mut s = session();
    let entry = |s: &mut Fx26Session, k: u32, text: &str| -> String {
        let forms = s.read_program(FileId(k), text).expect("reads");
        let mut last = String::new();
        for f in &forms {
            for o in s.run_each(f).expect("runs") {
                last = format!("{:?}", o.value);
            }
        }
        last
    };
    let twice = "(define-syntax twice (sc-macro-transformer (lambda (form env) \
                 (let ((e (make-syntactic-closure env '() (car (cdr form))))) `(+ ,e ,e)))))";
    entry(&mut s, 1, twice);
    let defined = fixpt_fx26::phase1::made();
    assert!(entry(&mut s, 2, "(twice 4)").contains('8'));
    let one = fixpt_fx26::phase1::made();
    assert!(one > defined, "a namespace for the entry that uses it");
    assert!(entry(&mut s, 3, "(+ (twice 1) (twice 2))").contains('6'));
    let two = fixpt_fx26::phase1::made();
    assert!(two > one, "another for the next");
    assert!(entry(&mut s, 4, "(+ 1 1)").contains('2'));
    assert_eq!(fixpt_fx26::phase1::made(), two, "none for an entry with no call");
}

/// The expander written in FX-26, checking a program the session's Rust
/// checker has read in the same expansion, calls the transformers the Rust
/// expander defined, the same closures: and both checkers agree.
#[test]
fn the_expander_written_in_fx26_calls_what_the_rust_one_defined() {
    let mut s = session();
    let dir = format!("{}/tests/programs/procedural", env!("CARGO_MANIFEST_DIR"));
    for name in ["aif-er.fx", "twice-sc.fx", "twice-rsc.fx", "split-er.fx"] {
        let text = std::fs::read_to_string(format!("{dir}/{name}")).expect("reads");
        s.read_program(FileId(0), &text).expect("the Rust checker reads it");
        let before = fixpt_fx26::phase1::called_for_fx26();
        let checked = s.check_with_own_checker(&text).expect("checks");
        assert!(checked.is_ok(), "{name}: {checked:?}");
        assert!(fixpt_fx26::phase1::called_for_fx26() > before, "{name}: called in phase 1");
    }
}

/// The expander written in FX-26, checking a program nothing has read
/// before, makes the namespace and defines each transformer there itself,
/// inside its own parse: the namespace's front end has a parser of its own
/// (the conductor makes each front end's), so the parse it is inside goes
/// on as it was, its macros defined.
#[test]
fn the_expander_written_in_fx26_defines_in_phase_1_inside_its_parse() {
    let dir = format!("{}/tests/programs/procedural", env!("CARGO_MANIFEST_DIR"));
    for name in ["aif-er.fx", "twice-sc.fx", "twice-rsc.fx", "split-er.fx"] {
        let mut s = session();
        let text = std::fs::read_to_string(format!("{dir}/{name}")).expect("reads");
        let (made, called) = (fixpt_fx26::phase1::made(), fixpt_fx26::phase1::called_for_fx26());
        let checked = s.check_with_own_checker(&text).expect("checks");
        assert!(checked.is_ok(), "{name}: {checked:?}");
        assert!(fixpt_fx26::phase1::made() > made, "{name}: a namespace made");
        assert!(fixpt_fx26::phase1::called_for_fx26() > called, "{name}: called in phase 1");
    }
}

/// Both checkers on a program (`fixpt check`, the comparisons): the Rust one
/// a fresh checker of the session's heap (`Fx26Session::fresh`), so both
/// call their transformers in one namespace, made once: the same closures.
#[test]
fn both_checkers_call_their_transformers_in_one_namespace() {
    let dir = format!("{}/tests/programs/procedural", env!("CARGO_MANIFEST_DIR"));
    let mut s = session();
    // The transformers' session, which the FX-26 expander's definitions are
    // checked in, made first: its namespace, once a thread, not counted.
    let first = std::fs::read_to_string(format!("{dir}/twice-rsc.fx")).expect("reads");
    fixpt_fx26::compare::both_checkers(&mut s, &first).expect("checks");
    for name in ["aif-er.fx", "twice-sc.fx", "split-er.fx"] {
        let text = std::fs::read_to_string(format!("{dir}/{name}")).expect("reads");
        let made = fixpt_fx26::phase1::made();
        let (fx26, rust) = fixpt_fx26::compare::both_checkers(&mut s, &text).expect("checks");
        assert!(matches!((&fx26, &rust), (Ok(a), Ok(b)) if a == b), "{name}: {fx26:?} {rust:?}");
        assert_eq!(fixpt_fx26::phase1::made(), made + 1, "{name}: one namespace for both");
    }
}
