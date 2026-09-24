//! Continuation marks, prompts and composable continuations (SRFI 226).
//!
//! Every case runs on both engines. They implement these features against very
//! different machines — frames that record "argument 2 of 3" in one, `(pc, fp)`
//! and call modes in the other — so agreement is the evidence that the shared
//! representation in `cmarks` means the same thing to both.
//!
//! The first cases are the properties checked against Racket 9.3 in
//! `reference/continuation-marks.rkt`; the expected answers are Racket's.

use fixpt_engine::Backend;
use fixpt_scheme::Session;

fn both(src: &str) -> String {
    let mut answers = Vec::new();
    for backend in [Backend::Ast, Backend::Bytecode] {
        let mut s = Session::with_backend(backend);
        answers.push(match s.eval_to_string("<test>", src) {
            Ok(v) => v,
            Err(e) => format!("!! {e}"),
        });
    }
    assert_eq!(answers[0], answers[1], "the engines disagree on:\n{src}");
    answers.pop().expect("two answers")
}

// ------------------------------------------------------------------ marks

#[test]
fn a_mark_in_tail_position_replaces_rather_than_accumulates() {
    // Racket: `(0)`. A tail loop marks the same frame each time round; if
    // marks stacked, this would be every depth, and the loop would not run in
    // constant space.
    let n = if cfg!(feature = "gc-stress") { 50 } else { 5_000 };
    assert_eq!(
        both(&format!(
            "(define (loop n)
               (with-continuation-mark 'depth n
                 (if (= n 0)
                     (continuation-mark-set->list (current-continuation-marks) 'depth)
                     (loop (- n 1)))))
             (loop {n})"
        )),
        "(0)"
    );
}

#[test]
fn marks_on_distinct_frames_accumulate_innermost_first() {
    assert_eq!(
        both(
            "(define (nontail n)
               (with-continuation-mark 'depth n
                 (if (= n 0)
                     (continuation-mark-set->list (current-continuation-marks) 'depth)
                     (car (list (nontail (- n 1)))))))
             (nontail 3)"
        ),
        "(0 1 2 3)"
    );
}

#[test]
fn a_mark_is_gone_once_its_frame_returns() {
    assert_eq!(
        both(
            "(define (probe) (continuation-mark-set-first #f 'k 'none))
             (list (car (list (with-continuation-mark 'k 'set (probe))))
                   (probe))"
        ),
        "(set none)"
    );
}

#[test]
fn introspection_stops_at_the_prompt() {
    assert_eq!(
        both(
            "(define tag (make-continuation-prompt-tag 'p))
             (with-continuation-mark 'k 'outside
               (car (list
                 (call-with-continuation-prompt
                   (lambda ()
                     (with-continuation-mark 'k 'inside
                       (car (list (continuation-mark-set->list
                                    (current-continuation-marks tag) 'k)))))
                   tag))))"
        ),
        "(inside)"
    );
}

// ---------------------------------------------------------------- prompts

#[test]
fn abort_delivers_values_to_the_handler() {
    assert_eq!(
        both(
            "(define tag (make-continuation-prompt-tag))
             (call-with-continuation-prompt
               (lambda () (+ 1 (abort-current-continuation tag 10 20)))
               tag
               (lambda (a b) (list 'handled a b)))"
        ),
        "(handled 10 20)"
    );
}

#[test]
fn a_prompt_returns_its_thunks_value_when_nothing_aborts() {
    assert_eq!(
        both("(+ 1 (call-with-continuation-prompt (lambda () 41)))"),
        "42"
    );
}

#[test]
fn abort_without_a_matching_prompt_is_an_error() {
    let out = both("(abort-current-continuation (make-continuation-prompt-tag) 1)");
    assert!(out.contains("no prompt"), "{out}");
}

#[test]
fn aborting_runs_after_thunks_innermost_first() {
    assert_eq!(
        both(
            "(define tag (make-continuation-prompt-tag))
             (define log '())
             (define (note x) (set! log (cons x log)))
             (call-with-continuation-prompt
               (lambda ()
                 (dynamic-wind (lambda () (note 'in1))
                   (lambda ()
                     (dynamic-wind (lambda () (note 'in2))
                       (lambda () (abort-current-continuation tag 'gone))
                       (lambda () (note 'out2))))
                   (lambda () (note 'out1))))
               tag
               (lambda (v) (note v)))
             (reverse log)"
        ),
        "(in1 in2 out2 out1 gone)"
    );
}

/// An `after` thunk runs in the dynamic context of its own `dynamic-wind`: the
/// handlers and marks installed *outside* it are live, the ones installed
/// inside are not. That is the reason abort leaves one extent at a time
/// rather than running every `after` from where the abort was called.
#[test]
fn an_after_thunk_sees_the_context_of_its_dynamic_wind() {
    assert_eq!(
        both(
            "(define tag (make-continuation-prompt-tag))
             (define seen '())
             (call-with-continuation-prompt
               (lambda ()
                 (with-exception-handler (lambda (e) 'outer-handler)
                   (lambda ()
                     (with-continuation-mark 'm 'outer-mark
                       (dynamic-wind
                         (lambda () #f)
                         (lambda ()
                           (with-exception-handler (lambda (e) 'inner-handler)
                             (lambda ()
                               (with-continuation-mark 'm 'inner-mark
                                 (car (list (abort-current-continuation tag 'x)))))))
                         (lambda ()
                           (set! seen (list (raise-continuable 'probe)
                                            (continuation-mark-set-first #f 'm)))))))))
               tag
               (lambda (v) v))
             seen"
        ),
        "(outer-handler outer-mark)"
    );
}

// ------------------------------------------------ composable continuations

#[test]
fn a_composable_continuation_can_be_inspected_and_resumed_repeatedly() {
    assert_eq!(
        both(
            "(define tag (make-continuation-prompt-tag))
             (define held #f)
             (call-with-continuation-prompt
               (lambda ()
                 (with-continuation-mark 'ctx 'here
                   (+ 100 (call-with-composable-continuation
                            (lambda (k) (set! held k) (abort-current-continuation tag 0))
                            tag))))
               tag
               (lambda (v) v))
             (list (continuation-mark-set->list (continuation-marks held tag) 'ctx)
                   (held 1)
                   (held 2)
                   (* 2 (held 3)))"
        ),
        "((here) 101 102 206)"
    );
}

/// Composing a captured segment re-enters its `dynamic-wind` extents, but not
/// the ones it is composed into, which are already live.
#[test]
fn resuming_a_composable_continuation_re_enters_its_extents() {
    assert_eq!(
        both(
            "(define tag (make-continuation-prompt-tag))
             (define log '())
             (define (note x) (set! log (cons x log)))
             (define held #f)
             (call-with-continuation-prompt
               (lambda ()
                 (dynamic-wind (lambda () (note 'in))
                   (lambda ()
                     (call-with-composable-continuation
                       (lambda (k) (set! held k) (abort-current-continuation tag 'stop))
                       tag))
                   (lambda () (note 'out))))
               tag
               (lambda (v) (note v)))
             (note (held 'again))
             (reverse log)"
        ),
        "(in out stop in out again)"
    );
}

#[test]
fn call_cc_still_winds_on_escape_and_reentry() {
    assert_eq!(
        both(
            "(define log '())
             (define (note x) (set! log (cons x log)))
             (define k #f)
             (define n 0)
             (dynamic-wind (lambda () (note 'in))
                           (lambda () (call/cc (lambda (c) (set! k c))) (set! n (+ n 1)))
                           (lambda () (note 'out)))
             (if (< n 2) (k 'again))
             (list n (reverse log))"
        ),
        "(2 (in out in out))"
    );
}

// ------------------------------------------------ the top level's prompt

/// The bug that motivated all this: handlers and extents were globals, and a
/// line abandoned by an uncaught error left them set for the next line.
#[test]
fn an_abandoned_input_leaves_no_handler_installed() {
    for backend in [Backend::Ast, Backend::Bytecode] {
        let mut s = Session::with_backend(backend);
        let first = s.eval_to_string(
            "<1>",
            "(with-exception-handler (lambda (e) 'stale) (lambda () (vector-ref (vector) 'x)))",
        );
        assert!(first.is_err(), "{backend:?}: {first:?}");
        let second = s.eval_to_string("<2>", "(raise-continuable 5)");
        assert!(
            matches!(&second, Err(e) if e.to_string().contains("uncaught")),
            "{backend:?}: a later input was handled by an abandoned one: {second:?}"
        );
    }
}

#[test]
fn an_uncaught_error_runs_the_after_thunks_it_escapes() {
    for backend in [Backend::Ast, Backend::Bytecode] {
        let mut s = Session::with_backend(backend);
        let (printed, result) = s.eval_capturing(
            "<1>",
            "(dynamic-wind (lambda () (display \"in \"))
                           (lambda () (car '()))
                           (lambda () (display \"out\")))",
        );
        assert!(result.is_err(), "{backend:?}");
        assert_eq!(printed, "in out", "{backend:?}");
        assert_eq!(
            s.eval_to_string("<2>", "(length (%current-winders))").ok().as_deref(),
            Some("0"),
            "{backend:?}: an extent outlived its input"
        );
    }
}

/// `current-continuation-marks` at the top level sees the form's marks and
/// none of the REPL's.
#[test]
fn the_top_level_contributes_no_marks() {
    assert!(both("(current-continuation-marks)").contains("mark-set"));
    assert_eq!(
        both("(continuation-mark-set->list (current-continuation-marks) 'anything)"),
        "()"
    );
}

// ------------------------------------------------------------------ holes

/// A hole captures the rest of its form as a composable continuation, up to
/// the top level's prompt, and hands it back instead of a value. Resuming
/// delivers a value to it — as often as you like, since it is a copy.
#[test]
fn a_hole_is_held_and_can_be_resumed_repeatedly() {
    for backend in [Backend::Ast, Backend::Bytecode] {
        let mut s = Session::with_backend(backend);
        s.eval_to_string("<1>", "(define v (vector 10 20 30))").expect("defines");
        let reached = s.eval_to_string("<2>", "(list 'got (vector-ref v (%hole 2 2)))");
        let Err(fixpt_scheme::SessionError::Hole(report)) = &reached else {
            panic!("{backend:?}: expected a hole, got {reached:?}");
        };
        assert!(report.contains("#(10 20 30)"), "{backend:?}: {report}");
        for (i, want) in [(0, "(got 10)"), (2, "(got 30)"), (1, "(got 20)")] {
            let v = s.resume("<resume>", &i.to_string()).expect("resumes");
            assert_eq!(fixpt_runtime::write_value(&s.rt.heap, v), want, "{backend:?}");
        }
    }
}

/// The hole reports what a program chose to mark, read out of the captured
/// continuation — the controllable half of introspection.
#[test]
fn a_hole_reports_the_marks_around_it() {
    for backend in [Backend::Ast, Backend::Bytecode] {
        let mut s = Session::with_backend(backend);
        let reached = s.eval_to_string(
            "<1>",
            "(with-continuation-mark 'processing 'record-17 (+ 1 (%hole 2 2)))",
        );
        let Err(fixpt_scheme::SessionError::Hole(report)) = &reached else {
            panic!("{backend:?}: expected a hole, got {reached:?}");
        };
        assert!(report.contains("processing = record-17"), "{backend:?}: {report}");
    }
}

/// Reaching a hole leaves the extents around it, and resuming re-enters them.
#[test]
fn a_hole_unwinds_on_the_way_out_and_rewinds_on_resume() {
    for backend in [Backend::Ast, Backend::Bytecode] {
        let mut s = Session::with_backend(backend);
        s.eval_to_string("<1>", "(define log '())").expect("defines");
        let reached = s.eval_to_string(
            "<2>",
            "(dynamic-wind (lambda () (set! log (cons 'in log)))
                           (lambda () (* 10 (%hole 2 2)))
                           (lambda () (set! log (cons 'out log))))",
        );
        assert!(matches!(reached, Err(fixpt_scheme::SessionError::Hole(_))), "{backend:?}");
        assert_eq!(s.eval_to_string("<3>", "(reverse log)").ok().as_deref(), Some("(in out)"));
        let v = s.resume("<resume>", "4").expect("resumes");
        assert_eq!(fixpt_runtime::write_value(&s.rt.heap, v), "40", "{backend:?}");
        assert_eq!(
            s.eval_to_string("<4>", "(reverse log)").ok().as_deref(),
            Some("(in out in out)"),
            "{backend:?}"
        );
    }
}

/// A hole reached while resuming another is caught at the *current* input's
/// prompt, like any other — the delimiter is reinstated around the resumed
/// continuation, which is the deep-handler reading of `shift0`.
#[test]
fn a_hole_reached_after_resuming_comes_back_to_the_top_level() {
    for backend in [Backend::Ast, Backend::Bytecode] {
        let mut s = Session::with_backend(backend);
        let first = s.eval_to_string("<1>", "(list 'a (%hole 2 2) (%hole 3 3))");
        assert!(matches!(first, Err(fixpt_scheme::SessionError::Hole(_))), "{backend:?}");
        let second = s.resume("<resume>", "1");
        assert!(matches!(second, Err(fixpt_scheme::SessionError::Hole(_))), "{backend:?}: {second:?}");
        let v = s.resume("<resume>", "2").expect("resumes");
        assert_eq!(fixpt_runtime::write_value(&s.rt.heap, v), "(a 1 2)", "{backend:?}");
    }
}
