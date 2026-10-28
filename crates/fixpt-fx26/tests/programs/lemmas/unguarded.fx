; Rejected: a proof that uses itself before rebuilding anything proves nothing.
(define-generative (tree (a type)) (oneof (leaf a) (node (tupof (l (tree a)) (r (tree a))))))
(define bad (proves (poly ((a type) (b type)) (<= (tree a) (tree b)) (<= a b)))
  (lambda (f t) (bad f t)))
