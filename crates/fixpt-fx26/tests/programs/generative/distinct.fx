; Rejected: a `dvar` is not a `ty-id`, though both are ints inside.
(define-generative ty-id int)
(define-generative dvar int)
(define f (subr pure (ty-id) int) (lambda (x) (down-ty-id x)))
(f (up-dvar 3))
