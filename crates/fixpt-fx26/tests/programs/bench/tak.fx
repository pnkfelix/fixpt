;;; Takeuchi: calls, with three arguments.
(define tak (subr spin (int int int) int)
  (lambda (x y z) (if (not (< y x)) z (tak (tak (- x 1) y z) (tak (- y 1) z x) (tak (- z 1) x y)))))
(tak 22 16 8)
