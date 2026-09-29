;;; FIB -- A classic benchmark, computes fib(n) inefficiently.
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/fib.scm),
;;; ported to FX-26. Larceny's input: 5 iterations of (fib 40).
;;; Answer: 102334155.

(define* fib (subr spin (int) int)
  (lambda (n)
    (if (< n 2)
        n
        (+ (fib (- n 1))
           (fib (- n 2))))))

;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace.
(define input int 40)
(define iterations int 5)

(define* run (subr spin (int int) int)
  (lambda (i result) (if (= i 0) result (run (- i 1) (fib input)))))
(run iterations 0)
