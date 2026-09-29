;;; A `cellular` procedure given where a `native` one is expected: the checker
;;; inserts the conversion.
(define inc (subr pure (int) int) (lambda (x) (+ x 1)))
(define n (subr (conv native) pure (int) int) inc)
