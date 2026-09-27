; Rejected: a contravariant parameter goes the other way.
(define-generative (sink (t type -)) (subr pure (t) int))
(define a (sink (sumof (a int) (b bool))) (up-sink (lambda (x) 1)))
(define b (sink (sumof (a int))) a)
(define c (sink (sumof (a int) (b bool) (c char))) a)
