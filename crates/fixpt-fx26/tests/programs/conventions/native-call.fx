;;; A `native` procedure called from `cellular` code: as through `fx`, the
;;; call looking at its callee's kind.
(define call (subr pure ((subr (conv native) pure (int) int)) int) (lambda (f) (f 1)))
