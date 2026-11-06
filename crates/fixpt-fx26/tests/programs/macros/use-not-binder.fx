;; ! a use of `let1`
;; A binder where the signature wants one, given an expression.
(define-syntax let1
  ((bvar expr) (import expr (rho (AA var))))
  ((_ (x e) body) (let ((x e)) body)))
(let1 ((f 1) 2) 3)
