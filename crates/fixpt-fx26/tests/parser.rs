//! The parser written in FX-26 (`src/parser.fx`) makes the Rust parser's
//! trees, desugarings and spans included (`PLAN.md` §11, step 9a).

use fixpt_engine::Backend;
use fixpt_fx26::Checker;
use fixpt_fx26::sexp::{Chars, show_top};
use fixpt_fx26::session::Fx26Session;
use fixpt_read::FileId;

/// The Rust parser's trees for `text`, checking each form as it goes, which
/// is how the Rust side parses.
fn rust_trees(text: &str) -> Vec<String> {
    let mut c = Checker::new();
    let forms = c.read_in(FileId(0), text).expect("reads");
    c.declare_ahead(&forms).expect("declares");
    let mut c2 = Checker::new();
    let forms2 = c2.read_in(FileId(0), text).expect("reads");
    let chars = Chars::of(text);
    let mut out = Vec::new();
    for f in &forms2 {
        let top = c2.top(f).unwrap_or_else(|e| panic!("checks: {e}"));
        out.push(show_top(&c2, &chars, &top, f.span));
    }
    out
}

fn same_trees(s: &mut Fx26Session, text: &str) {
    let ours = s.parse_with_own_parser(text).unwrap_or_else(|e| panic!("the FX-26 parser: {e}"));
    let rust = rust_trees(text);
    assert_eq!(ours.len(), rust.len(), "different numbers of forms");
    for (a, b) in ours.iter().zip(&rust) {
        assert_eq!(a, b, "the parsers disagree");
    }
}

#[test]
fn the_parsers_agree_on_small_programs() {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    for text in [
        "(+ 1 2)",
        "(define x int 5) (define y (+ x 1)) (if #t x y)",
        "(let* ((a 1) (b (+ a 1))) (and (= a b) (or #f #t) (and)))",
        "(cond ((= 1 2) 'no) (else 'yes))",
        "(the (subr pure (int bool) unit) (lambda ((x int) y) x #u))",
        "(product (a 1) (2 #\\c)) (sum t \"s\") (extract (product (a 1)) a)",
        "(tagcase (the (sumof (a int) (b (productof (1 int) (2 int)))) (sum a 1)) (a n n) (b (x y) (+ x y)))",
        "(tagcase (the (sumof (a int) (b int)) (sum a 1)) (a n n) (else r 0))",
        "(bloblet-ref (make-bloblet 0 1 2) 1)",
        "(letrec ((f (subr pure (int) int) (lambda (n) n))) (f 1))",
        "(proj (plambda ((r region)) (lambda () 1)) @q)",
        "(define-generative (box (t type +)) (productof (v t))) (down-box (up-box (product (v 1))))",
        "(define f (subr pure ((listof int const)) int) (lambda (xs) (acyclic xs (ok 1) 0)))",
    ] {
        same_trees(&mut s, text);
    }
}

#[test]
fn the_parsers_agree_on_real_programs() {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    for text in [
        include_str!("programs/bidirectional/twice.fx"),
        include_str!("programs/bloblet/point.fx"),
        include_str!("programs/bloblet/array-sum.fx"),
        include_str!("programs/bloblet/else-narrows.fx"),
        include_str!("programs/modules/counter.fx"),
        include_str!("programs/modules/parameter.fx"),
        include_str!("programs/modules/rec.fx"),
        include_str!("programs/modules/select.fx"),
        include_str!("programs/modules/transparent.fx"),
        fixpt_fx26::TABLE,
    ] {
        same_trees(&mut s, text);
    }
}

#[test]
fn a_parse_error_says_where() {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    let err = s.parse_with_own_parser("(if 1 2)").expect_err("too short");
    assert_eq!(err.message, "`(if test then else)`");
    assert_eq!((err.span.start, err.span.end), (0, 8));
    let err = s.parse_with_own_parser("(cond (#t 1))").expect_err("no else");
    assert!(err.message.contains("must end with an `else`"), "{}", err.message);
}

/// A `module` or a `with` the parsers refuse, each saying the same, at the
/// same place, as the Rust checker reading it.
#[test]
fn module_parse_errors_agree() {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    for text in [
        "(module (define))",
        "(module 5)",
        "(module (define-rec 5))",
        "(module (define-rec (f int)))",
        "(module (define-generative (t) int))",
        "(module (define-type 3 int))",
        "(with (module (define x 1)) x)",
        "(with)",
        "(define m (module)) (with m)",
    ] {
        let ours = s.parse_with_own_parser(text).expect_err("refused");
        let mut c = Checker::new();
        let forms = c.read_in(FileId(0), text).expect("reads");
        let rust = forms.iter().find_map(|f| c.top(f).err()).expect("refused");
        assert_eq!((ours.message, ours.span.start, ours.span.end), (rust.message, rust.span.start, rust.span.end), "{text}");
    }
}

/// What the comparison compares, spelled out once.
#[test]
fn a_tree_as_text() {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    let text = "(let* ((a #t)) (and a #f))";
    let ours = s.parse_with_own_parser(text).expect("parses");
    assert_eq!(
        ours,
        ["(t-exp (e-let ([a (e-bool #t 10 12)]) (e-if (e-var a 20 21) (e-bool #f 22 24) (e-bool #f 15 25) 15 25) 7 13))"]
    );
    assert_eq!(ours, rust_trees(text));
}
