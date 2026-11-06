;; => ("2" "bb")
;; Distributed in turn where a field is a product itself.
(define-type twice (allof (productof (inner (productof (g (subr pure (int) int)))) (k int))
                          (productof (inner (productof (g (subr pure (string) string)))) (k int))))
(define t twice
  (product (inner (product (g (lambda (x) (if (int? x) (* x 2) (string-append x x))))))
           (k 1)))
(define g (extract (extract t inner) g))
(list (int->string (g 1)) (g "b"))
