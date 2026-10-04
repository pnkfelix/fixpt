;; => (4)
;; A description function, `dlambda`, named by `define-type`, and applied:
;; `(twice box int)` is `(productof (v (productof (v int))))`.
(define-type twice (dlambda ((f (=> type type)) (a type)) (f (f a))))
(define-type (box (t type)) (productof (v t)))
(define b (twice box int) (product (v (product (v 4)))))
(list (extract (extract b v) v))
