;;; A lemma: if a ≤ b then (tree a) ≤ (tree b). Its proof rebuilds the tree it
;;; is given, tag for tag; nothing calls it, and the invariant tree widens.
(define-generative (tree (a type)) (sumof (leaf a) (node (tupleof (tree a) (tree a)))))
(define* tree-up (proves (poly ((a type) (b type)) (<= (tree a) (tree b)) (<= a b)))
  (lambda (f t)
    (up-tree (tagcase (down-tree t)
               (leaf x (sum leaf (f x)))
               (node (l r) (sum node (tuple (tree-up f l) (tree-up f r))))))))
(define small (tree (sumof (x int))) (up-tree (sum leaf (sum x 1))))
(define wide (tree (sumof (x int) (y bool))) small)
