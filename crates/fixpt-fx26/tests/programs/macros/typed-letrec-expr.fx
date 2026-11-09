;; ! is placed where a lambda is wanted
;; A typed `expr` hole where `letrec` wants a lambda: refused where the macro
;; is defined; it says it is a lambda, `(lambda #:type T)`.
(define-syntax call-rec
  ((bvar #:type (subr pure (int) int))
   (import (expr #:type (subr pure (int) int)) (rho (A var))))
  (syntax-rules ()
    ((_ f e) (letrec ((f (subr pure (int) int) e)) (f 3)))))
1
