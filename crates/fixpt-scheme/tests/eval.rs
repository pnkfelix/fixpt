//! `eval` (`session/eval.rs`): data a running program made, expanded and
//! compiled as a top-level form and run, on both engines alike.

use fixpt_engine::Backend;
use fixpt_scheme::Session;

fn both(src: &str) -> String {
    let mut out = Vec::new();
    for backend in [Backend::Ast, Backend::Bytecode] {
        let mut s = Session::with_backend(backend);
        let v = match s.eval_str("<test>", src) {
            Ok(h) => s.write(h),
            Err(e) => format!("error: {e}"),
        };
        out.push(v);
    }
    assert_eq!(out[0], out[1], "the engines disagree on:\n{src}");
    out.pop().expect("two")
}

#[test]
fn data_is_evaluated_in_the_session() {
    assert_eq!(both("(define x 10) (eval '(+ x 1))"), "11");
    assert_eq!(both("(eval (list '* 6 7) (interaction-environment))"), "42");
}

#[test]
fn a_definition_evaluated_lasts() {
    assert_eq!(both("(eval '(define y 5)) (+ y 1)"), "6");
}

#[test]
fn eval_within_eval() {
    assert_eq!(both("(eval '((lambda (n) (eval (list '+ n n))) 21))"), "42");
}

#[test]
fn a_macro_of_the_session_expands() {
    assert_eq!(both("(define-syntax twice (syntax-rules () ((_ e) (+ e e)))) (eval '(twice 4))"), "8");
}

#[test]
fn what_does_not_expand_is_an_error_the_program_catches() {
    assert_eq!(
        both("(guard (e ((error-object? e) (error-object-message e))) (eval '(if)))"),
        "\"<eval>:1:1: `if` takes a test and one or two branches\""
    );
}

#[test]
fn what_fails_as_it_runs_is_the_programs_error() {
    assert_eq!(both("(guard (e ((error-object? e) 'caught)) (eval '(car 1)))"), "caught");
}

#[test]
fn only_the_one_environment() {
    assert_eq!(both("(guard (e ((error-object? e) 'refused)) (eval 1 'elsewhere))"), "refused");
}

#[test]
fn what_is_not_code_is_refused() {
    assert_eq!(
        both("(guard (e ((error-object? e) (error-object-message e))) (eval (list 'quote (lambda () 1))))"),
        "\"eval: not code: #<procedure>\""
    );
}
