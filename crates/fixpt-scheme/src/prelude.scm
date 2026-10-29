;;; The fixpt prelude.
;;;
;;; Everything here could have been a primitive and deliberately is not. Two
;;; groups are worth pointing at:
;;;
;;; * `call/cc`, `dynamic-wind`, prompts, continuation marks,
;;;   `with-exception-handler`, `raise` and `raise-continuable`: the engine
;;;   provides raw mechanism that knows nothing about winding or handlers, and
;;;   the discipline is expressed here, in Scheme, where it is short enough to
;;;   check against R7RS and SRFI 226 by eye.
;;;
;;; * `map`, `for-each`, `assoc`, `member` and the `caar` family are ordinary
;;;   list code. Written here they automatically get proper tail calls and
;;;   behave correctly under `call/cc`; written in Rust each would need that
;;;   argued separately.
;;;
;;; It is in three files, read in this order: this one, the `c[ad]r` family;
;;; `prelude-data.scm`, the list, number, string and vector procedures; and
;;; `prelude-control.scm`, the control. A session that runs no lowered code
;;; can do with the first and last (`PRELUDE_CONTROL`).

;;; ------------------------------------------------------------------ lists

(define (caar p) (car (car p)))
(define (cadr p) (car (cdr p)))
(define (cdar p) (cdr (car p)))
(define (cddr p) (cdr (cdr p)))
(define (caaar p) (car (caar p)))
(define (caadr p) (car (cadr p)))
(define (cadar p) (car (cdar p)))
(define (caddr p) (car (cddr p)))
(define (cdaar p) (cdr (caar p)))
(define (cdadr p) (cdr (cadr p)))
(define (cddar p) (cdr (cdar p)))
(define (cdddr p) (cdr (cddr p)))
(define (cadddr p) (car (cdddr p)))
(define (cddddr p) (cdr (cdddr p)))
