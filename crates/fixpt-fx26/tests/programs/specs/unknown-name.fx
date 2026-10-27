; Refused
;;; A proposition names only the parameters and the result.
(define f (subr pure ((x : int)) int (requires (< 0 y))) (lambda (x) x))
