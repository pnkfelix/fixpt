;; => 7
;; A `race` branch that fails is lost, not the race's failure: the other
;; branch, which waits for an I-cell a process fills, gives the value.
(define a (icell int @c) (make-icell))
(define w (addr int @p) (spawn (box int r) (icell-put! a (receive box))))
(send w 7)
(race (error "no answer here") (icell-get a))
