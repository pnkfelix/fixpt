;;; A convention binder takes a convention, and nothing else.
(define app (poly ((c conv)) (subr pure ((subr (conv c) pure (int) int) int) int))
  (plambda ((c conv)) (lambda (f x) (f x))))
(proj app pure)
