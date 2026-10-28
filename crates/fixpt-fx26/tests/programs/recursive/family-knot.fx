;;; A type family that mentions itself with its own parameters: a knot,
;;; as `dletrec` ties, not an expansion without end.
(define-type (tree (r region)) (oneof (leaf int) (node (listof (tree r) r))))
(define leaf1 (poly ((r region)) (subr pure (int) (tree r)))
  (plambda ((r region)) (lambda (n) (one leaf n))))
(leaf1 3)
