;;; Two new types with the same representation: each is only itself.
(define-generative ty-id int #:seal up-ty-id #:unseal down-ty-id)
(define-generative dvar int #:seal up-dvar #:unseal down-dvar)
(define t (up-ty-id 3))
(define* f (subr pure (ty-id) int) (lambda (x) (+ (down-ty-id x) 1)))
(f t)
