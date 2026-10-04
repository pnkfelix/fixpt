;; ! `f` cannot be inferred
;; `(f a)` against a product: no function is solved for (FX-91's choice,
;; and Jones's), so `proj` must say what `f` is.
(define id (poly ((f (=> type type)) (a type)) (subr pure ((f a)) (f a)))
  (plambda ((f (=> type type)) (a type)) (lambda (x) x)))
(id (product (v 3)))
