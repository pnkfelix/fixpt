;; ! it may not end
;; A typed template that says its recursive binding ends is refused where it
;; is defined: a lambda a use gives may call it, without end.
(define-syntax call-rec
  (macro (_ f @ (bvar #:type (subr pure (int) int))
            e @ (lambda #:type (subr pure (int) int)))
         expr
    (bind f in e))
  (syntax-rules
    ((_ f e) (letrec ((f (subr pure (int) int) e)) (f 3)))))
1
