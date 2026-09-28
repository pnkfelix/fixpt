;;; A thunk given where a parameter's type is not yet known says what it
;;; is, as any argument does: there is nothing to tell it.
(define count-of (poly ((t type)) (subr pure (t) int))
  (plambda ((t type)) (lambda (x) 1)))
(count-of (lambda () (lambda ((f (subr pure (int) int)) (x int)) (f x))))
