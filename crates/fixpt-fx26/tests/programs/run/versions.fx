;;; Versions: `step` inlines `sum2`, which inlines `dbl`; its fast version
;;; assumes all three hold what they held, behind one guard each at its
;;; start, and so is a leaf, the constants folded through the inlined
;;; bodies. `run` calls itself in tail position: in its fast version, a loop.
(define* dbl (subr pure (int) int) (lambda (x) (+ x x)))
(define* sum2 (subr pure (int int) int) (lambda (a b) (+ (dbl a) (dbl b))))
(define* step (subr pure (int int) int) (lambda (acc i) (- (+ acc (sum2 i 2)) (dbl i))))
(define* run (subr spin (int int int) int)
  (lambda (i n acc) (if (= i n) acc (run (+ i 1) n (step acc i)))))
(run 0 1000 0)
