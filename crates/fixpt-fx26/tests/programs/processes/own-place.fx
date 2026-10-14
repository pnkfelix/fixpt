;; => 30
;; Each process keeps what it is sent in a reap of its own, waiting for its
;; next message inside it; two of them, interleaved, each end their own reap
;; in their own time (per-task place stacks, Q1).
(define half (icell int @t) (make-icell))
(define total (icell int @t) (make-icell))
(define* adder
  (poly ((r place))
    (subr (maxeff (receive r) nondet (init @t) spin) ((inbox int r) (icell int @t)) unit))
  (plambda ((r place))
    (lambda (box cell)
      (letreap q
        (let* ((a (rcons q (receive box) nil))
               (b (rcons q (receive box) a)))
          (icell-put! cell (+ (car a) (car b))))))))
(define p1 (addr int @a) (spawn (box int r) ((proj adder r) box half)))
(define p2 (addr int @a) (spawn (box int r) ((proj adder r) box total)))
(send p1 1)
(send p2 10)
(send p1 4)
(send p2 15)
(+ (icell-get half) (icell-get total))
