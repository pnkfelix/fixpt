//! The top level: definitions that stay in scope, and checking that does not.

use fixpt_fx26::{Checker, Top};
use fixpt_read::FileId;

fn top(c: &mut Checker, text: &str) -> Result<Top, String> {
    let forms = c.read_in(FileId(0), text).map_err(|e| e.message)?;
    c.top(&forms[0]).map_err(|e| e.message)
}

fn ty_of(c: &mut Checker, text: &str) -> String {
    match top(c, text) {
        Ok(Top::Exp(k)) => format!("{} ! {}", c.show_ty(k.ty), c.show_effect(&k.effect)),
        other => panic!("{other:?}"),
    }
}

#[test]
fn a_definition_stays_in_scope() {
    let mut c = Checker::new();
    top(&mut c, "(define double (subr pure (int) int) (lambda ((x int)) (+ x x)))").expect("defines");
    // Calling `double` reads the global.
    assert_eq!(ty_of(&mut c, "(double 4)"), "int ! (read (globals double))");
}

#[test]
fn a_typed_definition_may_be_recursive() {
    let mut c = Checker::new();
    let src = "(define* count (subr spin (int) int)
                 (lambda ((n int)) (if (= n 0) 0 (count (- n 1)))))";
    top(&mut c, src).expect("defines");
    assert_eq!(ty_of(&mut c, "(count 3)"), "int ! (maxeff spin (read (globals count)))");
}

#[test]
fn an_untyped_definition_takes_its_expressions_type() {
    let mut c = Checker::new();
    top(&mut c, "(define three 3)").expect("defines");
    assert_eq!(ty_of(&mut c, "(+ three 1)"), "int ! (read (globals three))");
}

#[test]
fn a_definition_that_does_not_match_its_type_is_rejected_and_not_kept() {
    let mut c = Checker::new();
    let err = top(&mut c, "(define x int #t)").expect_err("mismatch");
    assert!(err.contains("declared a int"), "{err}");
    assert!(top(&mut c, "x").is_err(), "a rejected definition stayed in scope");
}

#[test]
fn a_type_abbreviation_may_mention_itself() {
    let mut c = Checker::new();
    top(&mut c, "(define-type K (subr (goto @k) (K) void))").expect("defines");
    let written_out = c.type_of_str("(dletrec ((k (subr (goto @k) (k) void))) k)").expect("a type");
    let named = c.type_of_str("K").expect("a type");
    assert!(c.subtype(named, written_out) && c.subtype(written_out, named));
}

#[test]
fn a_type_abbreviation_that_is_only_a_name_is_rejected() {
    let mut c = Checker::new();
    let err = top(&mut c, "(define-type L L)").expect_err("ungrounded");
    assert!(err.contains("constructor"), "{err}");
    assert!(c.type_of_str("L").is_err(), "a rejected abbreviation stayed in scope");
}

#[test]
fn trying_a_form_leaves_nothing_behind() {
    let mut c = Checker::new();
    let forms = c.read_in(FileId(0), "(define y 5) (define-type T (ref int @r))").expect("reads");
    for f in &forms {
        let ok = c.try_top(f, |_, r| r.is_ok());
        assert!(ok);
    }
    assert!(top(&mut c, "y").is_err(), "a tried definition stayed");
    assert!(c.type_of_str("T").is_err(), "a tried abbreviation stayed");
}

#[test]
fn the_argument_a_subroutine_wants() {
    let mut c = Checker::new();
    let forms = c.read_in(FileId(0), "(+ 1 2) (cons 1 2)").expect("reads");
    let items = |f: &fixpt_read::Syntax| f.as_proper_list().expect("a list").to_vec();
    assert_eq!(c.describe_argument(&items(&forms[0]), 2).as_deref(), Some("int"));
    // Only what the other arguments determine is filled in.
    assert_eq!(c.describe_argument(&items(&forms[1]), 2).as_deref(), Some("t2"));
}

/// A form tried leaves no `->*` behind either: a type read from `->*` in
/// the try, its id then given to another type, does not make that one's
/// effect found instead of taken as written.
#[test]
fn trying_an_arrow_star_leaves_nothing_behind() {
    let mut c = Checker::new();
    let tried = c.read_in(FileId(0), "(letrec ((g (->* (int) int) (lambda (x) x))) (g 1))").expect("reads");
    assert!(c.try_top(&tried[0], |_, r| r.is_ok()));
    let written = "(letrec ((g (subr pure (int) int) (the (subr pure (int) int) (lambda (x) x)))) (g 1))";
    assert_eq!(ty_of(&mut c, written), "int ! pure");
}

/// A file loaded in a form tried leaves no load behind: the driver forgets
/// the symbols the try read (the REPL's notes as you type), so a load kept
/// would name its hidden global by a symbol gone, and a second try panic.
#[test]
fn trying_a_load_leaves_nothing_behind() {
    let mut c = Checker::new();
    let tried = c.read_in(FileId(0), "(load-module \"fx26:conditions.fx\")").expect("reads");
    for _ in 0..2 {
        let mark = c.interner.len();
        assert!(c.try_top(&tried[0], |_, r| r.is_ok()));
        c.interner.truncate(mark);
    }
    assert!(ty_of(&mut c, "(load-module \"fx26:conditions.fx\")").starts_with("(moduleof"));
}

/// A form refused leaves no file it loaded behind: a module file refused
/// for making state, after loading a pure one, is refused the same way
/// again, not taken the second time as though the pure one were made.
#[test]
fn refused_loads_leave_nothing_behind() {
    let mut c = Checker::new();
    c.base_dir = Some(std::path::PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs/module-files")));
    let form = c.read_in(FileId(0), "(load-module \"stateful-nested.fx\")").expect("reads");
    let first = c.top_defining(&form[0]).expect_err("refused").message;
    assert!(first.starts_with("a loaded file is one value for all its loads"), "{first}");
    let again = c.top_defining(&form[0]).expect_err("refused again").message;
    assert_eq!(again, first);
    // Tried as it is typed first, its symbols forgotten after, as the REPL
    // does: then refused the same way.
    let mut d = Checker::new();
    d.base_dir = c.base_dir.clone();
    let form = d.read_in(FileId(0), "(load-module \"stateful-nested.fx\")").expect("reads");
    let mark = d.interner.len();
    let tried = d.try_top(&form[0], |_, r| r.err().map(|e| e.message));
    d.interner.truncate(mark);
    assert_eq!(tried.as_deref(), Some(first.as_str()));
    assert_eq!(d.top_defining(&form[0]).expect_err("refused").message, first);
}
