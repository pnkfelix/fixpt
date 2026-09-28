;;; Nor converted to `native` explicitly.
(define inc (subr pure (int) int) (lambda (x) (+ x 1)))
(convention native inc)
