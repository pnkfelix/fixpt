;; ! argument 1 is a (anyof (pairof int (listof int acyclic) acyclic) (pairof bool
;; Pairs of which neither is above the other: `car` cannot choose one, and
;; taking the argument apart member by member is U3's (logical-types.md
;; §8.5, rule 5).
(define-type ib (anyof (listof int acyclic) (listof bool acyclic)))
(define first (subr pure (ib) int) (lambda (l) (if (null? l) 0 (if (car l) 1 2))))
