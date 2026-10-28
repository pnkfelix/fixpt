; Rejected: a generative type is invariant, and no lemma says otherwise.
(define-generative (tree (a type)) (oneof (leaf a) (node (tupof (l (tree a)) (r (tree a))))))
(define small (tree (oneof (x int))) (up-tree (one leaf (one x 1))))
(define wide (tree (oneof (x int) (y bool))) small)
