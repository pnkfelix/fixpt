;; => 3
;; A constructor binder found by matching: `(f a)` against `(gbox int)`
;; finds `f` to be `gbox`. Nothing else is solved for (`cannot-infer.fx`).
(define id (poly ((f (=> (type) type)) (a type)) (subr pure ((f a)) (f a)))
  (plambda ((f (=> (type) type)) (a type)) (lambda (x) x)))
(define-generative (gbox (t type)) (tupof (v t)))
(extract (down-gbox (id (up-gbox (tup (v 3))))) v)
