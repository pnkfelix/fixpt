; Rejected: a cycle through `poly`s alone describes no type, and unfolding
; it would never end.
(define-type t (poly ((a type)) t))
(define f (subr pure (t) int) (lambda (x) 0))
(define g (subr pure (t) int) (lambda (x) (f x)))
