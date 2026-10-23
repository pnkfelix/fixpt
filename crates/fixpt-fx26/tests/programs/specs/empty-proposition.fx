; Refused
;;; `()` is no proposition.
(define f (subr pure ((x int)) int (requires ()))
  (lambda (x) x))
(f 1)
