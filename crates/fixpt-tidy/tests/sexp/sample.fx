;; A comment about `a`.
(define a (subr pure (int) int) (lambda (x) (b x)))
(define b (subr pure (int) int) (lambda (x) (+ x 1)))
(define-rec
  (c (subr pure (int) int) (lambda (n) (if (= n 0) 0 (d (- n 1)))))
  (d (subr pure (int) int) (lambda (n) (c n))))
(define s string "b is not a symbol here")
