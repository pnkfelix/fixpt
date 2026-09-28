;;; Two new types with the same representation: each is only itself.
(define-generative ty-id int)
(define-generative dvar int)
(define t (up-ty-id 3))
(define* f (subr pure (ty-id) int) (lambda (x) (+ (down-ty-id x) 1)))
(f t)
