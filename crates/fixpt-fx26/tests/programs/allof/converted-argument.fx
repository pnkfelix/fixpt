;; => 3
;; A procedure of another convention, converted for the member it fits.
(define inc-fx (subr (conv fx) pure (int) int) (lambda (x) (+ x 1)))
(define run (allof (subr pure ((subr pure (int) int) int) int)
                   (subr pure ((subr pure (string) string) string) string))
  (lambda (f x) (f x)))
(run inc-fx 2)
