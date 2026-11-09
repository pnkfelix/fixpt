;; ! it may not end
;; A typed template that says its recursive binding ends is refused where it
;; is defined: a lambda a use gives may call it, without end.
(define-syntax call-rec
  ((bvar #:type (subr pure (int) int))
   (import (lambda #:type (subr pure (int) int)) (rho (A var))))
  (syntax-rules ()
    ((_ f e) (letrec ((f (subr pure (int) int) e)) (f 3)))))
1
