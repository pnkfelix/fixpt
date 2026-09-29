;;; FIB -- doubly recursive Fibonacci.
;;;
;;; From MLton's benchmark suite (benchmark/tests/fib.sml, commit
;;; aa2fd1ad9b91), ported to FX-26. Iteration count (ours; MLton's driver
;;; was not fetched): 3 iterations of (fib 41).
;;; Answer: 165580141 (the original checks for it).

(define* fib (subr spin (int) int)
  (lambda (n)
    (cond ((= n 0) 0)
          ((= n 1) 1)
          (else (+ (fib (- n 1)) (fib (- n 2)))))))

;; The inputs, where no compiler can fold them: globals, which a later
;; definition may replace.
(define input int 41)
(define iterations int 3)

(define* run (subr spin (int int) int)
  (lambda (i result) (if (= i 0) result (run (- i 1) (fib input)))))
(run iterations 0)
