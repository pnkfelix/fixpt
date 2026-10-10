;; ! `x` is defined twice in this module
;; A module included gives a name the module defines: refused, not shadowed.
(define a (module (define x int 1)))
(define m (module (include a) (define x int 2)))
