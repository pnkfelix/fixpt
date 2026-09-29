;;; TAK -- A vanilla version of the TAKeuchi function.
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/tak.scm),
;;; ported to FX-26. Larceny's input: 1 iteration of (tak 40 20 11).
;;; Answer: 12.

(define* tak (subr spin (int int int) int)
  (lambda (x y z)
    (if (not (< y x))
        z
        (tak (tak (- x 1) y z)
             (tak (- y 1) z x)
             (tak (- z 1) x y)))))

;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace.
(define input1 int 40)
(define input2 int 20)
(define input3 int 11)
(define iterations int 1)

(define* run (subr spin (int int) int)
  (lambda (i result) (if (= i 0) result (run (- i 1) (tak input1 input2 input3)))))
(run iterations 0)
