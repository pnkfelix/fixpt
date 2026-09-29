;;; CPSTAK -- A continuation-passing version of the TAK benchmark.
;;; A good test of first class procedures and tail recursion.
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/cpstak.scm),
;;; ported to FX-26. Larceny's input: 1 iteration of (cpstak 40 20 11).
;;; Answer: 12.

(define-type kont (subr spin (int) int))

(define cpstak (subr spin (int int int) int)
  (lambda (x y z)
    (letrec ((tak (subr spin (int int int kont) int)
               (lambda (x y z k)
                 (if (not (< y x))
                     (k z)
                     (tak (- x 1)
                          y
                          z
                          (lambda ((v1 int))
                            (tak (- y 1)
                                 z
                                 x
                                 (lambda ((v2 int))
                                   (tak (- z 1)
                                        x
                                        y
                                        (lambda ((v3 int))
                                          (tak v1 v2 v3 k)))))))))))
      (tak x y z (lambda ((a int)) a)))))

;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace.
(define input1 int 40)
(define input2 int 20)
(define input3 int 11)
(define iterations int 1)

(define* run (subr spin (int int) int)
  (lambda (i result) (if (= i 0) result (run (- i 1) (cpstak input1 input2 input3)))))
(run iterations 0)
