; Rejected: a subtree made from the wrong part does not even type-check.
(define-generative (tree (a type)) (oneof (leaf a) (node (tupof (l (tree a)) (r (tree a))))))
(define bad (proves (poly ((a type) (b type)) (<= (tree a) (tree b)) (<= a b)))
  (lambda (f t)
    (up-tree (tagcase (down-tree t)
               (leaf x (one leaf (f x)))
               (node (l r) (one node (tup (l l) (r l))))))))
