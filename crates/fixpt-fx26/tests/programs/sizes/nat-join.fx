;;; Branches of naturals of different sizes join at `nat`; `(>= n i)`
;;; shows `n - i ≥ 0`, so the difference is a natural.
(define pick (subr pure (bool nat) nat) (lambda (b n) (if b n 3)))
(define gap (subr pure (nat nat) nat) (lambda (n i) (if (>= n i) (- n i) (- i n))))
(+ (pick #t 4) (gap 2 9))
