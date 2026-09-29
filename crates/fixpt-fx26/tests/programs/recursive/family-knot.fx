;;; A type family that mentions itself with its own parameters: a knot,
;;; as `dletrec` ties, not an expansion without end.
(define-type (tree (r region)) (sumof (leaf int) (node (listof (tree r) r))))
(define leaf1 (poly ((r region)) (subr pure (int) (tree r)))
  (plambda ((r region)) (lambda (n) (sum leaf n))))
(leaf1 3)
