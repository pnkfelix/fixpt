; A recursive type through a `poly`, compared with itself under a product:
; the comparison ends, as the trail sees the pair again.
(define-type p1 (poly ((a type)) (subr pure (a) p1)))
(define f (subr pure ((productof (x p1))) int) (lambda (x) 0))
(define g (subr pure ((productof (x p1))) int) (lambda (x) (f x)))
