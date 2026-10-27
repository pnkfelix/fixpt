;; A module file.
(define* twice (subr pure (int) int)
  (lambda (n)
    (+ n n)))
