;; ! cannot be `finite` here
;; A size given to a description function, which may use it either way: not
;; one `finite` may stand for.
(define-type (box (t type)) (productof (v t)))
(define f (poly ((g (=> (type) type)) (s size)) (subr pure ((nat s) (g (nat s))) int))
  (plambda ((g (=> (type) type)) (s size)) (lambda (a b) 0)))
((proj f box finite) 3 (product (v 4)))
