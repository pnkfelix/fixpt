;; ! a `plambda` body must be pure
;; No cell is polymorphic (the value restriction), else one could be
;; projected at another type under each member of an `allof`.
(define c (poly ((t type)) (ref (listof t acyclic) @h)) (plambda ((t type)) (new nil)))
