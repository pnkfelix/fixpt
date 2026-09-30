; `a - c` is a natural where `a ≥ b` and `b ≥ c`: two facts chained, which
; takes Fourier–Motzkin elimination; both checkers do it, step for step
; (`src/sizes.rs`, `refuted_below`; `check-print.fx`, `k-refuted-below?`).
(define* f (subr pure (nat nat nat) nat)
  (lambda (a b c) (if (>= a b) (if (>= b c) (- a c) 0) 0)))
(f 5 3 1)
