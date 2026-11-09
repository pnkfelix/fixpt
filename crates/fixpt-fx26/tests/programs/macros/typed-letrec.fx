;; => 3
;; A typed hole where `letrec` wants a lambda is a `lambda` part: in the
;; template's check, a lambda calling its procedure, so it is checked once.
;; Given the recursive binding, the hole may call it: the template says it
;; may not end (`spin`), as it must for every lambda a use may give it.
(define-syntax call-rec
  ((bvar #:type (subr spin (int) int))
   (import (lambda #:type (subr spin (int) int)) (rho (A var))))
  (syntax-rules ()
    ((_ f e) (letrec ((f (subr spin (int) int) e)) (f 3)))))
(call-rec g (lambda ((n int)) n))
