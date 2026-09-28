;;; Generative types at run time: the conversions are the identity, and a
;;; tree walked through `down-tree` gives its sum.
(define-generative ty-id int)
(define-generative (tree (a type)) (sumof (leaf a) (node (productof (l (tree a)) (r (tree a))))))
(define* total (subr pure ((tree int)) int)
  (lambda (t) (tagcase (down-tree t) (leaf n n) (node (l r) (+ (total l) (total r))))))
(define* leaf (subr pure (int) (tree int)) (lambda (n) (up-tree (sum leaf n))))
(+ (down-ty-id (up-ty-id 40))
   (total (up-tree (sum node (product (l (leaf 1)) (r (leaf 1)))))))
