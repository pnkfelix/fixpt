; Rejected: a parameter is invariant unless declared otherwise.
(define-generative (box (t type)) (productof (v t)))
(define a (box (sumof (a int))) (up-box (product (v (sum a 1)))))
(define b (box (sumof (a int) (b bool))) a)
