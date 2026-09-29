;;; TAK -- the Takeuchi function.
;;;
;;; From MLton's benchmark suite (benchmark/tests/tak.sml, commit
;;; aa2fd1ad9b91), ported to FX-26. Iteration count (ours; MLton's driver
;;; was not fetched): 2 iterations of (tak 33 22 11).
;;; Answer: 22 (the original checks for it).
;;; SML's tuple argument (x, y, z) becomes three parameters.

(define* tak (subr spin (int int int) int)
  (lambda (x y z)
    (if (not (< y x))
        z
        (tak (tak (- x 1) y z)
             (tak (- y 1) z x)
             (tak (- z 1) x y)))))

;; The inputs, where no compiler can fold them: globals, which a later
;; definition may replace.
(define input1 int 33)
(define input2 int 22)
(define input3 int 11)
(define iterations int 2)

(define* run (subr spin (int int) int)
  (lambda (i result) (if (= i 0) result (run (- i 1) (tak input1 input2 input3)))))
(run iterations 0)
