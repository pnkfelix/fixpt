; Rejected: outside its conversions, a `ty-id` is not an int.
(define-generative ty-id int)
(define f (subr pure (ty-id) int) (lambda (x) (+ x 1)))
