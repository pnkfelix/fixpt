;; => 4
;; A typed binder: the body is a hole in its scope, given the variable.
(define-syntax let1
  (poly ((t type) (u type) (e1 effect) (e2 effect))
    (macro (_ (x @ (bvar #:type t) (expr #:type t #:effect e1))
              body @ (expr #:type u #:effect e2))
           expr
      (bind x in body)))
  (syntax-rules
    ((_ (x e) body) (let ((x e)) body))))
(let1 (n 3) (+ n 1))
