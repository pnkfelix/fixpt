; Rejected: a `dvar` is not a `ty-id`, though both are ints inside.
(define-generative ty-id int #:seal up-ty-id #:unseal down-ty-id)
(define-generative dvar int #:seal up-dvar #:unseal down-dvar)
(define* f (subr pure (ty-id) int) (lambda (x) (down-ty-id x)))
(f (up-dvar 3))
