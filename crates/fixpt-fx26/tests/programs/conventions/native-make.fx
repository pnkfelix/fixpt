;;; Nor can a procedure be made `native` yet.
(define inc (subr pure (int) int) (lambda (x) (+ x 1)))
(define n (subr (conv native) pure (int) int) inc)
