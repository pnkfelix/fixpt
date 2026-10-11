; Rejected: a `distinct` binder given a region the procedure's type mentions.
(define copy-in (poly ((r region distinct))
                  (subr (maxeff (read r) (write r) (read @heap))
                        ((ref int r) (ref int @heap))
                        unit))
  (plambda ((r region distinct)) (lambda (x y) (set x (get y)))))
(define h (ref int @heap) (new 1))
(copy-in h h)
