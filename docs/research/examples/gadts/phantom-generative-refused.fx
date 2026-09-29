; Refused: under a generative name (N1) the index is invariant (N2), so a
; list counted from zero is not one counted from one.
(define-type zero (sumof (zero unit)))
(define-type one (sumof (one unit)))
(define-generative (counted (i type)) (listof int acyclic))
(define from-zero (counted zero) (up-counted (list 0 1)))
(define from-one (counted one) from-zero)
