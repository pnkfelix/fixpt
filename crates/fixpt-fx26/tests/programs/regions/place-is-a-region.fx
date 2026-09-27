; A place is a region too: a `letrena`'s place names the region of the data
; made in it, and a procedure over any place can be given it.
(define total (poly ((p place)) (subr (maxeff (alloc p) (read p)) ((place p) int) int))
  (plambda ((p place))
    (lambda ((h (place p)) (n int))
      (car (the (listof int p) (rcons h n nil))))))
(letrena r ((proj total r) r 7))
