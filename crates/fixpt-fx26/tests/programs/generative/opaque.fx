; Rejected: outside its conversions, a `ty-id` is not an int.
(define-generative ty-id int #:seal up-ty-id #:unseal down-ty-id)
(define f (subr pure (ty-id) int) (lambda (x) (+ x 1)))
