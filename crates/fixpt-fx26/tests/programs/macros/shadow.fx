;; ! Herman's shadow restriction
;; Herman's `K`: at `(K x x)` the inner binder would capture the reference.
(define-syntax K
  (bvar bvar)
  ((_ a b) (lambda ((a int)) (lambda ((b int)) a))))
