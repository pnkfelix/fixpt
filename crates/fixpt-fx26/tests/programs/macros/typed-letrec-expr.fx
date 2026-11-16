;; ! is placed where a lambda is wanted
;; A typed `expr` hole where `letrec` wants a lambda: refused where the macro
;; is defined; it says it is a lambda, `(lambda #:type T)`.
(define-syntax call-rec
  (macro (_ f @ (bvar #:type (subr pure (int) int))
            e @ (expr #:type (subr pure (int) int)))
         expr
    (bind f in e))
  (syntax-rules
    ((_ f e) (letrec ((f (subr pure (int) int) e)) (f 3)))))
1
