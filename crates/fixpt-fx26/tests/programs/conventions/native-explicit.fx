;;; A procedure converted to `native` explicitly: an adapter, made when the
;;; conversion runs.
(define inc (subr pure (int) int) (lambda (x) (+ x 1)))
(convention native inc)
