;; ! is placed in the scope of other bindings than its signature says
;; Herman's `bad`: the body said to be in `a`'s scope, placed where no `a`
;; is bound.
(define-syntax bad
  ((bvar expr) (import expr (rho (AA var))))
  ((_ (a e) body) body))
