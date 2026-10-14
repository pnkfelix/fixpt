;; => 1
;; A loser is stopped at its next wait: the second branch waits for `b`,
;; and would spin for ever once `b` is filled; it is filled after the
;; first branch has won, and the program ends.
(define a (icell int @c) (make-icell))
(define b (icell int @c) (make-icell))
(define* spin-forever (subr spin () int) (lambda () (spin-forever)))
(define w (addr int @p) (spawn (box int r) (icell-put! a (receive box))))
(send w 1)
(define v int (race (icell-get a) (begin (icell-get b) (spin-forever))))
(icell-put! b 0)
v
