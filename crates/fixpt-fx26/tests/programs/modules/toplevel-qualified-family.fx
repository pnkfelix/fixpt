;; => 3
;; A family applied: the top level's `box`, not the `plambda`'s function.
(define-type (box (a type)) (listof a))
(define g (poly ((box (=> (type) type))) (subr pure (int) int))
  (plambda ((box (=> (type) type)))
    (lambda ((n int)) (length (the (#%toplevel:box int) (list n n n))))))
((proj g (dlambda ((a type)) a)) 5)
