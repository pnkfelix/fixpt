; Rejected: `(-> (param …) result)` is pure, so a procedure of that type
; may not run without end, as `(subr pure …)` may not.
(define forever (-> (int) int)
  (lambda (n) (forever n)))
(forever 0)
