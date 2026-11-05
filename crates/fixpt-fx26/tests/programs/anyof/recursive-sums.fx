;; => 6
;; A recursive type's sums, its own name inside their payloads: made one
;; sum, which `tagcase` takes apart.
(define-type tree
  (anyof (sumof (leaf int)) (sumof (node (productof (1 tree) (2 tree))))))
(define total (subr pure (tree) int)
  (letrec ((go (subr pure (tree) int)
             (lambda (t)
               (tagcase t (leaf n n) (node p (+ (go (extract p 1)) (go (extract p 2))))))))
    go))
(define leaf (subr pure (int) tree) (lambda (n) (sum leaf n)))
(define node (subr pure (tree tree) tree) (lambda (a b) (sum node (product (1 a) (2 b)))))
(total (node (leaf 1) (node (leaf 2) (leaf 3))))
