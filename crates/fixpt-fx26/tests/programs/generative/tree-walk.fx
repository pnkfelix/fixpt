;;; A tree walked through `down-tree` ends: size-change sees the
;;; conversions as the identity, and `tagcase` gives parts.
(define-type (pair (a type)) (tupleof a a))
(define-generative (nest (a type))
  (sumof (none unit) (more (tupleof a (nest (pair a))))))
(define-generative (tree (a type)) (sumof (leaf a) (node (tupleof (tree a) (tree a)))))
(define total (subr (read (globals down-tree)) ((tree int)) int)
  (letrec ((total (subr (read (globals down-tree)) ((tree int)) int)
             (lambda (t) (tagcase (down-tree t) (leaf n n) (node (l r) (+ (total l) (total r)))))))
    total))
(total (up-tree (sum node (tuple (up-tree (sum leaf 1)) (up-tree (sum leaf 2))))))
