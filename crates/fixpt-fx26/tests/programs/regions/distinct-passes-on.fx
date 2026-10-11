; Rejected: inside, `r1` is distinct, so `swap` takes it and `r2`; `r2` and
; `r3`, which may be one region, it does not.
(define-type swap-type
  (poly ((r1 region distinct) (r2 region))
    (subr (maxeff (read r1) (write r1) (read r2) (write r2)) ((ref int r1) (ref int r2)) unit)))
(define swap swap-type
  (plambda ((r1 region distinct) (r2 region))
    (lambda (a b) (let ((t (get a))) (begin (set a (get b)) (set b t))))))
(define twice (poly ((r1 region distinct) (r2 region) (r3 region))
                (subr (maxeff (read r1) (write r1) (read r2) (write r2) (read r3) (write r3))
                      ((ref int r1) (ref int r2) (ref int r3)) unit))
  (plambda ((r1 region distinct) (r2 region) (r3 region))
    (lambda (a b c) (begin (swap a b) (swap b c)))))
