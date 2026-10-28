;;; A lemma: if a ≤ b then (tree a) ≤ (tree b). Its proof rebuilds the tree it
;;; is given, tag for tag; nothing calls it, and the invariant tree widens.
(define-generative (tree (a type)) (oneof (leaf a) (node (tupof (l (tree a)) (r (tree a))))))
(define* tree-up (proves (poly ((a type) (b type)) (<= (tree a) (tree b)) (<= a b)))
  (lambda (f t)
    (up-tree (tagcase (down-tree t)
               (leaf x (one leaf (f x)))
               (node (l r) (one node (tup (l (tree-up f l)) (r (tree-up f r)))))))))
(define small (tree (oneof (x int))) (up-tree (one leaf (one x 1))))
(define wide (tree (oneof (x int) (y bool))) small)
