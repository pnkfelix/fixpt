; Rejected: the bound moves as the count does, so it bounds nothing.
(define f (subr pure (int int) int) (lambda (i n) (if (< i n) (f (+ i 1) (+ n 1)) i)))
