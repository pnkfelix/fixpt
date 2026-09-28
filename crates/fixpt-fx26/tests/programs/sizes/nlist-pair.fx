;;; A `nlist` of some length is a pair of an element and a `nlist` of some length.
(define v (nlist int finite) nil)
(define p (pairof int (nlist int finite) acyclic) v)
