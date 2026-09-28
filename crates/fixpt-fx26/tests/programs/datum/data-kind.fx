;;; A binder of kind `data` takes data: a list frozen `acyclic` of pairs of
;;; ints is; the identity at it is fine.
(define same (poly ((t data)) (subr pure (t) t)) (lambda (x) x))
(same (the (listof (productof (a int) (b bool)) acyclic) nil))
