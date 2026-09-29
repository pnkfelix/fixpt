;;; ACK -- One of the Kernighan and Van Wyk benchmarks.
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/ack.scm),
;;; ported to FX-26. Larceny's input: 2 iterations of (ack 3 12).
;;; Answer: 32765.

(define* ack (subr spin (int int) int)
  (lambda (m n)
    (cond ((= m 0) (+ n 1))
          ((= n 0) (ack (- m 1) 1))
          (else (ack (- m 1) (ack m (- n 1)))))))

;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace.
(define input1 int 3)
(define input2 int 12)
(define iterations int 2)

(define* run (subr spin (int int) int)
  (lambda (i result) (if (= i 0) result (run (- i 1) (ack input1 input2)))))
(run iterations 0)
