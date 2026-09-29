;;; TAILFIB -- Fibonacci by a tail-recursive loop.
;;;
;;; From MLton's benchmark suite (benchmark/tests/tailfib.sml, commit
;;; aa2fd1ad9b91), ported to FX-26. Iteration count (ours; MLton's driver
;;; was not fetched, and its doit runs n * 1000000 times): 1 iterations
;;; of (fib 44).
;;; Answer: 701408733 (the original checks for it).
;;; SML's tuple argument (n, a, b) becomes three parameters.

(define* fib* (subr spin (int int int) int)
  (lambda (n a b)
    (if (= n 0) a (fib* (- n 1) (+ a b) a))))
(define* fib (subr spin (int) int)
  (lambda (n) (fib* n 0 1)))

;; The inputs, where no compiler can fold them: globals, which a later
;; definition may replace.
(define input int 44)
(define iterations int 50000000)

(define* run (subr spin (int int) int)
  (lambda (i result) (if (= i 0) result (run (- i 1) (fib input)))))
(run iterations 0)
