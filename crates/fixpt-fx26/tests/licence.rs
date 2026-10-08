//! Effects as licences (`docs/fx26.md`, plan step 7): a speculation driver
//! runs FX-26 code before it is asked for only when the code's effect is
//! licensed — allocation anywhere, and reads, writes and control only on
//! regions the driver owns.

use fixpt_engine::Backend;
use fixpt_fx26::Checker;
use fixpt_fx26::licence::unlicensed;
use fixpt_fx26::session::{Fx26Session, Speculation, compile_program};
use fixpt_scheme::eager::{EagerReader, EagerStatus};

#[test]
fn the_licence_allows_allocation_and_what_the_driver_owns() {
    let mut c = Checker::new();
    let mine = c.region_named("@mine");
    let pure = c.effect_of_str("pure").expect("an effect");
    let alloc = c.effect_of_str("(alloc @theirs)").expect("an effect");
    let own = c.effect_of_str("(maxeff (read @mine) (write @mine) (goto @mine) (comefrom @mine))").expect("an effect");
    assert_eq!(unlicensed(&pure, &[]), None);
    assert_eq!(unlicensed(&alloc, &[]), None, "a new object is invisible until handed over");
    assert_eq!(unlicensed(&own, &[mine]), None);
    for bad in ["(read @theirs)", "(write @theirs)", "(goto @theirs)", "(comefrom @theirs)"] {
        let e = c.effect_of_str(bad).expect("an effect");
        assert!(unlicensed(&e, &[mine]).is_some(), "{bad} was licensed");
    }
}

#[test]
fn an_effect_variable_is_never_licensed() {
    let mut c = Checker::new();
    let t = c.type_of_str("(poly ((e effect)) (subr e () int))").expect("a type");
    let fixpt_fx26::ast::Ty::Poly { body, .. } = c.arena.get(t).clone() else { panic!() };
    let (e, _, _) = c.arena.get(body).as_subr().expect("a subroutine");
    assert!(unlicensed(&e, &[]).is_some());
}

// -------------------------------------------------------------- the REPL

fn session() -> Fx26Session {
    Fx26Session::with_backend(Backend::Bytecode).expect("starts")
}

fn speculate(s: &mut Fx26Session, text: &str) -> Speculation {
    let forms = s.checker.read_in(fixpt_read::FileId(0), text).expect("reads");
    s.speculate(&forms[0])
}

fn run(s: &mut Fx26Session, text: &str) {
    let forms = s.checker.read_in(fixpt_read::FileId(0), text).expect("reads");
    s.run(&forms[0]).expect("runs").value.expect("no error");
}

/// A pure expression runs early; one that allocates privately, too, since
/// masking has already removed what nobody else can see.
#[test]
fn a_licensed_expression_runs_early() {
    let mut s = session();
    assert_eq!(speculate(&mut s, "(+ 1 2)"), Speculation::Value("3".into()));
    assert_eq!(speculate(&mut s, "(car (cons 1 #t))"), Speculation::Value("1".into()));
    assert_eq!(speculate(&mut s, "(+ 1 (cwcc (lambda (k) (k 41))))"), Speculation::Value("42".into()));
}

/// A write to a cell the program shares is not run — and so did not happen.
#[test]
fn an_unlicensed_expression_is_not_run() {
    let mut s = session();
    run(&mut s, "(define c (ref int @c) (new 1))");
    assert_eq!(speculate(&mut s, "(set c 5)"), Speculation::NotLicensed("(write @c)".into()));
    assert_eq!(speculate(&mut s, "(get c)"), Speculation::NotLicensed("(read @c)".into()));
    run(&mut s, "(define* probe (subr (read @c) () int) (lambda () (get c)))");
    let forms = s.checker.read_in(fixpt_read::FileId(0), "(probe)").expect("reads");
    assert_eq!(s.run(&forms[0]).expect("runs").value, Ok(Some("1".into())), "the speculative write happened");
}

#[test]
fn definitions_and_errors_are_not_run() {
    let mut s = session();
    assert_eq!(speculate(&mut s, "(define x 3)"), Speculation::NotAnExpression);
    assert!(matches!(speculate(&mut s, "(+ 1 #t)"), Speculation::Rejected(_)));
    assert!(matches!(speculate(&mut s, "(car (the (listof int @l) nil))"), Speculation::Failed(_)));
    // Speculating kept nothing: `x` was never defined.
    assert!(matches!(speculate(&mut s, "x"), Speculation::Rejected(_)));
}

/// A loop is licensed — it is pure — and the budget stops it.
#[test]
fn a_speculative_run_has_a_budget() {
    let mut s = session();
    run(&mut s, "(define* spin (subr spin (int) int) (lambda (n) (spin n)))");
    assert!(matches!(speculate(&mut s, "(spin 0)"), Speculation::Failed(_)));
    // And the ordinary budget is back afterwards.
    assert_eq!(speculate(&mut s, "(+ 1 2)"), Speculation::Value("3".into()));
}

// ------------------------------------------------------------ the reader

/// The eager reader's every entry point stays within the regions its driver
/// owns — so it may run on every keystroke.
#[test]
fn the_eager_reader_is_licensed() {
    let mut compiled = compile_program(&fixpt_fx26::front_end()).expect("checks");
    compiled.checker.reader_licence().expect("licensed");
}

/// A reader that also touched a region its driver does not own is refused,
/// and the refusal says what it would have done.
#[test]
fn a_reader_that_reaches_outside_is_refused() {
    let doctored = format!(
        "{}\n(define shared (ref int @user) (new 0))
         (define* eager-feed (subr (write @user) (state char) state)
           (lambda (st ch) (begin (set shared 1) st)))",
        fixpt_fx26::front_end()
    );
    let mut compiled = compile_program(&doctored).expect("checks");
    let err = compiled.checker.reader_licence().expect_err("refused");
    assert_eq!(err, "`eager-feed` may (write @user), which is not the program's own to touch");
}

/// What licenses the reader is its type: a `plambda` over the regions it
/// is given, each entry point touching only those (`parametric_licence`).
/// One that touches a region of its own choosing, which the program it runs
/// beside could name, is refused, saying what it would have done.
#[test]
fn a_reader_that_names_a_region_of_its_own_is_refused() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs/module-files");
    let run = |file: &str| {
        let mut c = Checker::new();
        c.base_dir = Some(std::path::PathBuf::from(dir));
        c.check_program(&format!("(define make (load-module \"{file}\"))\n0")).expect("checks");
        c.parametric_licence("make", &["feed"])
    };
    run("licensed.fx").expect("licensed");
    let err = run("unlicensed.fx").expect_err("refused");
    assert_eq!(err, "`feed`, as `make` makes it, may (write @user), which is not among the regions it is given");
}

/// Loaded into an ordinary Scheme session — the Scheme REPL's — the FX-26
/// reader drives the line editor as the Scheme one does.
#[test]
fn the_fx26_reader_loads_into_a_scheme_session() {
    let compiled = compile_program(&fixpt_fx26::front_end()).expect("checks");
    let mut scheme = fixpt_scheme::Session::with_backend(Backend::Bytecode);
    compiled.load_into(&mut scheme).expect("loads");
    let mut r = EagerReader::attach(&mut scheme, "fx:").expect("starts");
    assert_eq!(r.status(&mut scheme, "(a b", false).expect("reads"), EagerStatus::Incomplete);
    assert_eq!(r.status(&mut scheme, "(a b)", false).expect("reads"), EagerStatus::Complete);
    assert!(matches!(r.status(&mut scheme, "(a b]", false).expect("reads"), EagerStatus::Invalid { at: 4, .. }));
}

/// Loaded beside a user's program, as the FX-26 REPL loads it, the reader
/// keeps to its own globals: a user who defines `need` and `advance` — the
/// reader's own names — does not replace the reader's.
#[test]
fn the_reader_beside_a_program_keeps_its_own_names() {
    let mut s = session();
    fixpt_fx26::session::load_eager_reader(&mut s.scheme).expect("licensed and loaded");
    let mut r = EagerReader::attach_starting(&mut s.scheme, fixpt_fx26::session::READER_PREFIX, "eager-start-fx26")
        .expect("starts");
    run(&mut s, "(define need 0)");
    run(&mut s, "(define advance (subr pure (int) int) (lambda (n) n))");
    assert_eq!(r.status(&mut s.scheme, "(f #u", false).expect("reads"), EagerStatus::Incomplete);
    assert_eq!(r.status(&mut s.scheme, "(f #u)", false).expect("reads"), EagerStatus::Complete);
}
