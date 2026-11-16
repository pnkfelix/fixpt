;; ! its type is written, `(bvar #:type T)`
;; A typed hole in an untyped binder's scope cannot be given its variable.
(define-syntax let1
  (macro (_ (x @ bvar (expr #:type int)) body @ (expr #:type int)) expr (bind x in body))
  (syntax-rules
    ((_ (x e) body) (let ((x e)) body))))
1
