;; ! is placed in the scope of `a`, but its signature says it is in no scope of the pattern's
;; The expression said to be outside `a`'s scope, placed inside it.
(define-syntax leaky
  (macro (_ (bvar expr) expr) expr)
  (syntax-rules
    ((_ (a e) body) (let ((a e)) body))))
