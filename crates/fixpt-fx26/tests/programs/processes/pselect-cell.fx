;; => 7
;; `pselect` over two I-cells, only one of which a process fills: whichever
;; order the tasks run in, the arm of the one filled is chosen.
(define never (icell int @c) (make-icell))
(define soon (icell int @c) (make-icell))
(define p (addr int @p) (spawn (box int r) (icell-put! soon (receive box))))
(send p 6)
(pselect ((icell-get never) x (* x 100))
        ((icell-get soon) y (+ y 1)))
