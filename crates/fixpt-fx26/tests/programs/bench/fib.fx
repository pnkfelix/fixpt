;;; Calls: doubly recursive, on ints.
(define fib (subr pure (int) int)
  (lambda (n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2))))))
(fib 30)
