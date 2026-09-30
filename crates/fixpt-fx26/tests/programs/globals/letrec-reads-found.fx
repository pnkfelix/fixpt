; A local `letrec`'s procedures need not name the globals they read: they
; are found, as `define*` finds a definition's (PLAN.md Q11). `a` calls
; `b`, which reads `twice`, so `a` reads it too, found in a second round.
(define* twice (subr pure (int) int) (lambda (n) (* 2 n)))
(define* f (subr pure (nat) int)
  (lambda (n)
    (letrec ((a (subr pure (nat int) int)
               (lambda (i acc) (if (= i 0) acc (b (- i 1) acc))))
             (b (subr pure (nat int) int)
               (lambda (i acc) (if (= i 0) acc (a (- i 1) (twice acc))))))
      (a n 1))))
(f 10)
