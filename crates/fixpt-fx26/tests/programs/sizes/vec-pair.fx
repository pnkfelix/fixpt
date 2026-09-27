;;; A `vec` of some length is a pair of an element and a `vec` of some length.
(define v (vec int finite) nil)
(define p (pairof int (vec int finite) finite) v)
