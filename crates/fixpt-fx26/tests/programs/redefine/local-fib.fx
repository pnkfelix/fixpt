;;; A procedure that must call itself, whatever its global comes to hold,
;;; binds itself locally.
(define fib (subr spin (int) int)
  (letrec ((fib (subr spin (int) int) (lambda (n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2)))))))
    fib))
(fib 20)
