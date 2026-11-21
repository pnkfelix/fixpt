;; A maker of a module of an abstract type (`docs/research/dependent-moduleof.md`):
;; each module made its own `t`.
(module-parameters ())
(define-generative t int #:seal up-t #:unseal down-t)
(define zero t (up-t 0))
(define* next (subr pure (t) t) (lambda (x) (up-t (+ (down-t x) 1))))
(define* value (subr pure (t) int) (lambda (x) (down-t x)))
