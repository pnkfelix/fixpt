;;; Counting down a `nat`: in the `else` of `(= n 0)` the checker knows
;;; `n ≥ 1`, so `(- n 1)` is a natural; and a `nat` never goes below 0, so
;;; the recursion ends.
(define count (subr pure (nat) int)
  (letrec ((count (subr pure (nat) int)
             (lambda (n) (if (= n 0) 0 (+ 1 (count (- n 1)))))))
    count))
(define below (subr pure (nat nat) nat)
  (lambda (i n) (if (< i n) (- n i) 0)))
(count (below 3 10))
