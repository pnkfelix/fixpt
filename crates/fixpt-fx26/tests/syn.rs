//! The reader written in FX-26 feeding the checker (`PLAN.md` §11, step 8):
//! what it reads, spans and all, is what the Rust reader reads, and a
//! program read by it checks and runs.

use fixpt_engine::Backend;
use fixpt_fx26::session::Fx26Session;
use fixpt_read::{FileId, Reader, SyntaxProfile};

/// Both readers on `text`, into the same interner, so the syntax compares
/// whole: data, and every span.
fn same_syntax(s: &mut Fx26Session, text: &str) {
    let ours = s.read_with_own_reader(text).unwrap_or_else(|e| panic!("the FX-26 reader: {e}"));
    let rust = Reader::new(text, FileId(0), SyntaxProfile::FX26, &mut s.checker.interner).read_all().expect("reads");
    let rust = s.checker.expand_forms(rust).expect("expands");
    assert_eq!(ours.len(), rust.len(), "different numbers of forms");
    for (a, b) in ours.iter().zip(&rust) {
        assert_eq!(a, b, "the readers disagree");
    }
}

#[test]
fn the_readers_agree_spans_and_all() {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    for text in [
        "(f #u #u8(1 2) #t #f Foo \"str\\n\" #\\a #\\space 'q) #| c |# #;(gone) (g . h) #(1 (2))",
        "(λ \"ünïcode\" x) ; a comment\n(after)",
        include_str!("programs/bloblet/expr.fx"),
        include_str!("programs/bidirectional/twice.fx"),
        fixpt_fx26::TABLE,
    ] {
        same_syntax(&mut s, text);
    }
}

#[test]
fn a_program_read_by_fx26_checks_and_runs() {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    let v = s.run_program_read_by_fx26(include_str!("programs/bloblet/expr.fx")).expect("checks");
    assert_eq!(v, Ok("42".to_string()));
}

#[test]
fn a_reading_error_says_where() {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    let err = s.read_with_own_reader("(a b))").expect_err("unbalanced");
    assert!(err.message.contains("unbalanced"), "{}", err.message);
    assert_eq!(err.span.start, 5);
    let err = s.read_with_own_reader("(a (b").expect_err("unfinished");
    assert!(err.message.contains("middle of a form"), "{}", err.message);
}
