;; A module of no parameters, for `module-parameters`' modules.
(define* twice (subr pure (int) int) (lambda (x) (* 2 x)))
(define-type pt (productof (x int) (y int)))
