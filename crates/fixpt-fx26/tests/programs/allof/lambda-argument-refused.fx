;; ! argument 1 is a string, where a int is expected
;; Checked against each member it fits: under the `string` one, `y` is no
;; `int` for `+`.
(define both (allof (subr pure ((subr pure (int) int)) (subr pure (int) int))
                    (subr pure ((subr pure (string) string)) (subr pure (string) string)))
  (lambda (f) (lambda (x) (f x))))
(both (lambda (y) (+ y 1)))
