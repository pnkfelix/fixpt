;;; SUM -- Compute sum of integers from 0 to 10000
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/sum.scm),
;;; ported to FX-26. Larceny's input: 200000 iterations of (run 10000).
;;; Answer: 50005000.
;;;
;;; Larceny's procedure `run` is `sum-to` here, since the driver below is
;;; `run`; its named-let accumulator `sum` is `acc`, since `sum` is an
;;; FX-26 form.

(define* sum-to (subr spin (int) int)
  (lambda (n)
    (letrec ((loop (subr spin (int int) int)
               (lambda (i acc)
                 (if (< i 0)
                     acc
                     (loop (- i 1) (+ i acc))))))
      (loop n 0))))

;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace.
(define input1 int 10000)
(define iterations int 200000)

(define* run (subr spin (int int) int)
  (lambda (i result) (if (= i 0) result (run (- i 1) (sum-to input1)))))
(run iterations 0)
