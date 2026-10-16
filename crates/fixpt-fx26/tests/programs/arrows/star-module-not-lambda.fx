; Rejected: in a module too, `->*` finds a procedure's effect from its
; `lambda`.
(define m (module (define inc (-> (int) int) (lambda (x) (+ x 1)))
                  (define also (->* (int) int) inc)))
((with m also) 1)
