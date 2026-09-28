;;; Nothing yet calls a `native` procedure from `cellular` code.
(define call (subr pure ((subr (conv native) pure (int) int)) int) (lambda (f) (f 1)))
