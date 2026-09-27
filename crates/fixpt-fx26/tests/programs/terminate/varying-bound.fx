; Rejected: a bound that changes with each call bounds nothing.
(define f (subr pure (int) int) (lambda (n) (let ((c (- n 5))) (if (> n c) (f (- n 1)) 0))))
