;; ! a (anyof (listof int acyclic) (listof bool acyclic)) is expected here, and this is a string
;; Members that a test cannot tell apart: printed `anyof`.
(define v (anyof (listof int acyclic) (listof bool acyclic)) "neither")
