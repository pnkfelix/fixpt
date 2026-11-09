;; ! its type is written, `(bvar #:type T)`
;; A typed hole in an untyped binder's scope cannot be given its variable.
(define-syntax let1
  ((bvar (expr #:type int)) (import (expr #:type int) (rho (AA var))))
  (syntax-rules ()
    ((_ (x e) body) (let ((x e)) body))))
1
