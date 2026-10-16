; Rejected: `->*` finds a procedure's effect from its `lambda`.
(define inc (-> (int) int) (lambda (x) (+ x 1)))
(define also (->* (int) int) inc)
(also 1)
