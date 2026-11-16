;; ! `AA` is an address in Herman's letters: an address is `(path #:a #:d …)`, its steps from the root
;; Herman's form, its addresses its letters: paths now, first step first.
(define-syntax let1
  (macro/addressed ((bvar expr) (import expr (rho (AA var)))) expr)
  (syntax-rules ((_ (x e) body) (let ((x e)) body))))
