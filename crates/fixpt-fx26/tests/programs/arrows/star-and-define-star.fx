; Rejected: `define*` and `->*` each find what a procedure does.
(define* inc (->* (int) int) (lambda (x) (+ x 1)))
(inc 1)
