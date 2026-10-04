;; ! is a description function, of kind (=> (type) type): it is applied
;; A type constructor is no type: it is applied.
(define g (poly ((f (=> (type) type))) (subr pure (f) int))
  (plambda ((f (=> (type) type))) (lambda (x) 1)))
