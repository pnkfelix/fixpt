; Rejected: `->*` finds a procedure's effect from its `lambda`, and a
; `plambda` is not one.
(define f (-> (int) int)
  (lambda (n)
    (letrec ((id (->* (int) int) (plambda () (lambda (k) k))))
      (id n))))
(f 3)
