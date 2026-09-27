;;; A `vec` of two is a pair of an element and a `vec` of one.
(define v (vec int 2) (cons 1 (cons 2 nil)))
(define p (pairof int (vec int 1) finite) v)
