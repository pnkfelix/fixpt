; Rejected: `(f (f x))` does not type-check, `f` taking an `a`; the error names
; argument 1 in both checkers, though the type is called `a`.
(define-generative (tree (a type)) (oneof (leaf a) (node (tupof (l (tree a)) (r (tree a))))))
(define bad (proves (poly ((a type) (b type)) (<= (tree a) (tree b)) (<= a b)))
  (lambda (f t)
    (up-tree (tagcase (down-tree t)
               (leaf x (one leaf (f (f x))))
               (node (l r) (one node (tup (l (bad f l)) (r (bad f r)))))))))
