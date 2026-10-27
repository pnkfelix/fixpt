; Refused
;;; A `bool` is not an integer.
(define f (subr pure ((b : bool)) int (requires (< 0 b))) (lambda (b) 0))
