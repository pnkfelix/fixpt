; Rejected: a parameter is invariant unless declared otherwise.
(define-generative (box (t type)) (tupof (v t)))
(define a (box (oneof (a int))) (up-box (tup (v (one a 1)))))
(define b (box (oneof (a int) (b bool))) a)
