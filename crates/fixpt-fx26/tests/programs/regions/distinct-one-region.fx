; Rejected: a `distinct` binder given the region another binder is given.
(define-type swap-type
  (poly ((r1 region distinct) (r2 region))
    (subr (maxeff (read r1) (write r1) (read r2) (write r2)) ((ref int r1) (ref int r2)) unit)))
(define swap swap-type
  (plambda ((r1 region distinct) (r2 region))
    (lambda (a b) (let ((t (get a))) (begin (set a (get b)) (set b t))))))
(letregion r
  (let ((x (the (ref int r) (new 1))) (y (the (ref int r) (new 2))))
    (begin (swap x y) (get x))))
