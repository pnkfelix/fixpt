;; ! is not a lambda, as this part must be
;; A use whose expression is not a lambda where a `lambda` part is: refused
;; where it is written, before it is expanded.
(define-syntax call-rec
  (bvar (import lambda (rho (A var))))
  (syntax-rules ()
    ((_ f e) (letrec ((f (subr pure (int) int) e)) (f 3)))))
(call-rec g 5)
