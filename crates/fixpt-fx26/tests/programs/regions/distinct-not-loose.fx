; Rejected: a procedure that needs a `distinct` region is no procedure that
; does not; its callers promise less.
(define-type loose (poly ((r1 region) (r2 region))
                     (subr (maxeff (read r1) (write r2)) ((ref int r1) (ref int r2)) unit)))
(define-type tight (poly ((r1 region distinct) (r2 region))
                     (subr (maxeff (read r1) (write r2)) ((ref int r1) (ref int r2)) unit)))
(define inner tight (plambda ((r1 region distinct) (r2 region)) (lambda (a b) (set b (get a)))))
(define outer loose inner)
