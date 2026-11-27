;; A module file made by a call (it has state).
(module-parameters ())
(define-type t (productof (x int)))
(define mk (subr pure (int) t) (lambda ((n int)) (product (x n))))
(define r (ref int @ed) (new 0))
