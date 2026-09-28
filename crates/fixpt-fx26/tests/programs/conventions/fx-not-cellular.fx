;;; Inside a list, no conversion is inserted: an `fx` procedure is not a
;;; `cellular` one.
(define fs (listof (subr (conv fx) pure (int) int) const) (cons (lambda (x) x) nil))
(define gs (listof (subr pure (int) int) const) fs)
