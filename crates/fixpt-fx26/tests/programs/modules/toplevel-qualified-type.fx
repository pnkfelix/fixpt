;; => 6
;; `#%toplevel:idx` is the top level's `idx`, whatever binds `idx` where it
;; is written: the `define-type`'s `int`, not the `plambda`'s type variable.
(define-type idx int)
(define g (poly ((idx type)) (subr pure (idx) int))
  (plambda ((idx type)) (lambda ((x idx)) (+ (the #%toplevel:idx 5) 1))))
((proj g bool) #t)
