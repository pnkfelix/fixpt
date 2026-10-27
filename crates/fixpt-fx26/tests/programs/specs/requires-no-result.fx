; Refused
;;; A `requires` cannot name the result.
(define f (subr pure ((x : int)) int (requires (< 0 r)) (ensures r (< 0 r))) (lambda (x) 1))
