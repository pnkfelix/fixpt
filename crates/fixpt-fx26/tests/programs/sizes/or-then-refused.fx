; Rejected: the then of an `or` knows only a disjunction, `n ≥ 1` or
; `m ≥ 1`, which facts cannot say (that waits on logical types, PLAN.md
; Q7); so `(- n 1)` there is not known to be a natural.
(define* f (subr pure (nat nat) nat)
  (lambda (n m) (if (or (>= n 1) (>= m 1)) (- n 1) 0)))
(f 3 0)
