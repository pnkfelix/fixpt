; Two recursive types through a `poly`, the same but for the binders' names:
; equal, and the comparison ends.
(define-type p1 (poly ((a type)) (subr pure (a) p1)))
(define-type p2 (poly ((b type)) (subr pure (b) p2)))
(define f (subr pure ((productof (x p2))) int) (lambda (x) 0))
(define* g (subr pure ((productof (x p1))) int) (lambda (x) (f x)))
