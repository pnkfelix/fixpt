;; ! its type is written, `(lambda #:type (subr E (A …) R))`
;; A typed `lambda` part's stand-in is made of its type, written out.
(define-type fn (subr pure (int) int))
(define-syntax call-rec
  (macro (_ f @ (bvar #:type fn) e @ (lambda #:type fn)) expr (bind f in e))
  (syntax-rules
    ((_ f e) (letrec ((f fn e)) (f 3)))))
1
