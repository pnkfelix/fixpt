;; => ("5" "a" "7")
;; A `lambda` with parameters of no type, given an `allof`: it fits a member
;; whose parameter is a procedure of its arity, and is checked against what
;; the members it fits take there, their `allof` where they differ (`both`).
(define twice (allof (subr pure ((subr pure (int) int) int) int)
                     (subr pure ((subr pure (string) string) string) string))
  (lambda (f x) (f (f x))))
(define both (allof (subr pure ((subr pure (int) int)) (subr pure (int) int))
                    (subr pure ((subr pure (string) string)) (subr pure (string) string)))
  (lambda (f) (lambda (x) (f x))))
(define id (both (lambda (y) y)))
(list (int->string (twice (lambda (y) (+ y 1)) 3)) (id "a") (int->string (id 7)))
