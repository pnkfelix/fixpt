;; ! is placed in the scope of other bindings than its signature says
;; Herman's `bad`: the body said to be in `a`'s scope, placed where no `a`
;; is bound.
(define-syntax bad
  (macro (_ (a @ bvar expr) body @ expr) expr (bind a in body))
  (syntax-rules
    ((_ (a e) body) body)))
