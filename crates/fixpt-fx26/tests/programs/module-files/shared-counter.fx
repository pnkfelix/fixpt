;; A file of no state with an abstract type (`load-shared*.fx`).
(define-generative t int)
(define zero t (up-t 0))
(define value (subr pure (t) int) (lambda (v) (down-t v)))
