;;; Small helpers called in a loop, in the style of the front end's code:
;;; what inlining is for. (No `*`, which is a runtime primitive, so that the
;;; calls are what is timed.)
(define* dbl (subr pure (int) int) (lambda (x) (+ x x)))
(define* sum2 (subr pure (int int) int) (lambda (a b) (+ (dbl a) (dbl b))))
(define* step (subr pure (int int) int) (lambda (acc i) (- (+ acc (sum2 i 2)) (dbl i))))
(define* run (subr spin (int int int) int)
  (lambda (i n acc) (if (= i n) acc (run (+ i 1) n (step acc i)))))
(run 0 3000000 0)
