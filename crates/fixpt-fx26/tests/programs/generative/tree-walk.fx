;;; A tree walked through `down-tree` ends: size-change sees the
;;; conversions as the identity, and `tagcase` gives parts.
(define-generative (nest (a type)) (sumof (none unit) (more (productof (hd a) (tl (nest (productof (l a) (r a))))))))
(define-generative (tree (a type)) (sumof (leaf a) (node (productof (l (tree a)) (r (tree a))))))
(define total (subr (read (globals down-tree)) ((tree int)) int)
  (letrec ((total (subr (read (globals down-tree)) ((tree int)) int)
             (lambda (t) (tagcase (down-tree t) (leaf n n) (node (l r) (+ (total l) (total r)))))))
    total))
(total (up-tree (sum node (product (l (up-tree (sum leaf 1))) (r (up-tree (sum leaf 2)))))))
