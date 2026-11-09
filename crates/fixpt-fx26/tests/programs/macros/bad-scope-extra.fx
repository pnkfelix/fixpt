;; ! is placed in the scope of other bindings than its signature says
;; The expression said to be outside `a`'s scope, placed inside it.
(define-syntax leaky
  ((bvar expr) expr)
  (syntax-rules ()
    ((_ (a e) body) (let ((a e)) body))))
