; Rejected: `(= n 0)` bounds nothing when it fails, and `(f -1)` loops.
(define f (subr pure (int) int) (lambda (n) (if (= n 0) 0 (f (- n 1)))))
