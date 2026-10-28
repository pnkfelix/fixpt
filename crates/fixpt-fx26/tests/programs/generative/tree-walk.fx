;;; A tree walked through `down-tree` ends: size-change sees the
;;; conversions as the identity, and `tagcase` gives parts.
(define-type (pair (a type)) (tupof (l a) (r a)))
(define-generative (nest (a type))
  (oneof (none unit) (more (tupof (hd a) (tl (nest (pair a)))))))
(define-generative (tree (a type)) (oneof (leaf a) (node (tupof (l (tree a)) (r (tree a))))))
(define total (subr (read (globals down-tree)) ((tree int)) int)
  (letrec ((total (subr (read (globals down-tree)) ((tree int)) int)
             (lambda (t) (tagcase (down-tree t) (leaf n n) (node (l r) (+ (total l) (total r)))))))
    total))
(total (up-tree (one node (tup (l (up-tree (one leaf 1))) (r (up-tree (one leaf 2)))))))
