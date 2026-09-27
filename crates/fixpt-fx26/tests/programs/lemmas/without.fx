; Rejected: a generative type is invariant, and no lemma says otherwise.
(define-generative (tree (a type)) (sumof (leaf a) (node (productof (l (tree a)) (r (tree a))))))
(define small (tree (sumof (x int))) (up-tree (sum leaf (sum x 1))))
(define wide (tree (sumof (x int) (y bool))) small)
