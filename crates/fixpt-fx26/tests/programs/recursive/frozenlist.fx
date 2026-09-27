; Rejected: a mutable list is not a frozen one.
(define f (subr pure ((listof int const)) int) (lambda (x) 0))
(define g (subr pure ((listof int @r)) int) (lambda (x) (f x)))
