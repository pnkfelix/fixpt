; Rejected: a subtree made from the wrong part does not even type-check.
(define-generative (tree (a type)) (sumof (leaf a) (node (productof (l (tree a)) (r (tree a))))))
(define bad (proves (poly ((a type) (b type)) (<= (tree a) (tree b)) (<= a b)))
  (lambda (f t)
    (up-tree (tagcase (down-tree t)
               (leaf x (sum leaf (f x)))
               (node (l r) (sum node (product (l l) (r l))))))))
