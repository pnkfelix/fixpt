; Rejected: a contravariant parameter goes the other way.
(define-generative (sink (t type -)) (subr pure (t) int))
(define a (sink (oneof (a int) (b bool))) (up-sink (lambda (x) 1)))
(define b (sink (oneof (a int))) a)
(define c (sink (oneof (a int) (b bool) (c char))) a)
