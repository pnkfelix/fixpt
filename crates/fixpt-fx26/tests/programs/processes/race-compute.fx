;; => 55
;; `race` of three computations that give one answer, so which finishes
;; first does not matter to it.
(define* fib (subr spin (int) int) (lambda (n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2))))))
(define* fib-from (subr spin (int int int) int)
  (lambda (n a b) (if (= n 0) a (fib-from (- n 1) b (+ a b)))))
(race (fib 10) (fib-from 10 0 1) 55)
