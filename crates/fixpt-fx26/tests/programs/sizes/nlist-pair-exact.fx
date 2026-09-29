;;; A `nlist` of two is a pair of an element and a `nlist` of one.
;; cons-chain: an (nlist int n): list gives no size
(define v (nlist int 2) (cons 1 (cons 2 nil)))
(define p (pairof int (nlist int 1) acyclic) v)
