; Rejected: the region given is bound outside the place, so it could outlive
; it, and `build`'s bound refuses it.
(define build (poly ((p place) (r region p)) (subr (maxeff (alloc r) (alloc p)) ((place p) int) (listof int r)))
  (plambda ((p place) (r region p))
    (lambda ((h (place p)) (n int)) (rcons h n nil))))
(letregion d (letrena a (car ((proj build a d) a 1))))
