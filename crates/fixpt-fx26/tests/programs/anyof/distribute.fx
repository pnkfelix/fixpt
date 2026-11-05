;; => 1
;; An immutable pair of a union is the union of the pairs: shown by
;; splitting the pair at its head (logical-types.md §8.8).
(define-type pi (pairof int nil acyclic))
(define-type pb (pairof bool nil acyclic))
(define p (pairof (oneof int bool) nil acyclic) (cons 1 nil))
(define q (anyof pi pb) p)
(car p)
