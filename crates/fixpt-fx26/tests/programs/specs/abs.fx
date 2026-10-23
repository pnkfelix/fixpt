; Verified
;;; `abs`: its result is no less than 0, and is `x` or its negation. Each
;;; way out of the `if` returns, and proves the `ensures` there.
(define abs (subr pure ((x int)) int (ensures r (and (<= 0 r) (or (= r x) (= r (- x))))))
  (lambda (x) (if (< x 0) (- 0 x) x)))
(abs -5)
