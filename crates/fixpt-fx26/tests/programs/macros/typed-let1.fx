;; => 4
;; A typed binder: the body is a hole in its scope, given the variable.
(define-syntax let1
  (poly ((t type) (u type) (e1 effect) (e2 effect))
    (((bvar #:type t) (expr #:type t #:effect e1))
     (import (expr #:type u #:effect e2) (rho (AA var)))))
  (syntax-rules ()
    ((_ (x e) body) (let ((x e)) body))))
(let1 (n 3) (+ n 1))
