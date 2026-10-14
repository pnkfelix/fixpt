;; => 42
;; Preemption at fuel polls (`TODO.md` §92, Q2): a process that spins for
;; ever, started first, does not starve the one that answers. Without
;; preemption the spinner, run first, never gives the thread back, and the
;; program waits for ever.
(define answer (icell int @c) (make-icell))
(define* spin-forever (subr spin (int) int) (lambda (n) (spin-forever (+ n 1))))
(define spinner (addr int @p) (spawn (box int r) (begin (spin-forever (receive box)) #u)))
(define doubler (addr int @p) (spawn (box int r) (icell-put! answer (* 2 (receive box)))))
(send spinner 0)
(send doubler 21)
(icell-get answer)
