; Rejected: `(f (f x))` does not type-check, `f` taking an `a`; the error names
; argument 1 in both checkers, though the type is called `a`.
(define-generative (tree (a type)) (sumof (leaf a) (node (productof (l (tree a)) (r (tree a))))))
(define bad (proves (poly ((a type) (b type)) (<= (tree a) (tree b)) (<= a b)))
  (lambda (f t)
    (up-tree (tagcase (down-tree t)
               (leaf x (sum leaf (f (f x))))
               (node (l r) (sum node (product (l (bad f l)) (r (bad f r)))))))))
