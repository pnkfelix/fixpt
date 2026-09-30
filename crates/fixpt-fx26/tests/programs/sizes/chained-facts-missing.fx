; Rejected: with only `a ≥ b` known, `a - c` may be below 0, so it is an
; `int`, not a `nat`.
(define* f (subr pure (nat nat nat) nat)
  (lambda (a b c) (if (>= a b) (- a c) 0)))
(f 5 3 1)
