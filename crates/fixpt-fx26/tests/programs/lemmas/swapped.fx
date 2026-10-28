; Rejected: the subtrees are swapped, so this is not the identity.
(define-generative (tree (a type)) (oneof (leaf a) (node (tupof (l (tree a)) (r (tree a))))))
(define bad (proves (poly ((a type) (b type)) (<= (tree a) (tree b)) (<= a b)))
  (lambda (f t)
    (up-tree (tagcase (down-tree t)
               (leaf x (one leaf (f x)))
               (node (l r) (one node (tup (l (bad f r)) (r (bad f l)))))))))
