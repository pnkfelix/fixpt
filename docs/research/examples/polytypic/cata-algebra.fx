;;; PolyP's cata, with the functor fixed: FX-26 has no `type -> type`
;;; kind, so a fold cannot be generic in the functor. One fold per type
;;; (what a deriver would write), taking the algebra as a dictionary:
;;; a product with one function per constructor. Each generic-looking
;;; function is then an algebra, with no recursion of its own.
(define-datatype tree (leaf int) (node tree tree))
(define-type (tree-alg (b type) (e effect))
  (productof (leaf (subr e (int) b)) (node (subr e (b b) b))))
(define tree-cata
  (poly ((b type) (e effect)) (subr e ((tree-alg b e) tree) b))
  (lambda (alg t)
    (letrec ((go (subr e (tree) b)
               (lambda (t)
                 (tagcase t
                   (leaf (n) ((extract alg leaf) n))
                   (node (l r) ((extract alg node) (go l) (go r)))))))
      (go t))))
(define size-alg (tree-alg int pure)
  (product (leaf (lambda (n) 1)) (node (lambda (x y) (+ x y)))))
(define depth-alg (tree-alg int pure)
  (product (leaf (lambda (n) 0)) (node (lambda (x y) (+ 1 (if (< x y) y x))))))
(define t1 tree (node (leaf 1) (node (leaf 2) (leaf 3))))
(tree-cata size-alg t1)
(tree-cata depth-alg t1)
