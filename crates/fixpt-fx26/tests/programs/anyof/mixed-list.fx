;; ! is expected here, and this is a (listof ib acyclic)
;; A list of either is not a list of one or a list of the other: splitting
;; its first pair leaves a tail of mixed elements, below neither.
(define-type ib (oneof int bool))
(define l (listof ib acyclic) (list 1 #t))
(define m (anyof (listof int acyclic) (listof bool acyclic)) l)
