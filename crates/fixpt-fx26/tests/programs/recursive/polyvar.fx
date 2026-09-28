; A recursive type through a `poly`, as a parameter's type, given a value of
; that type.
(define-type p1 (poly ((a type)) (subr pure (a) p1)))
(define f (subr pure (p1) int) (lambda (x) 0))
(define* g (subr pure (p1) int) (lambda (x) (f x)))
