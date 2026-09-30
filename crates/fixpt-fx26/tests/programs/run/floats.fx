;;; `f64` literals and operations, lowered, compiled and evaluated alike.
(define* newton (subr spin (f64 f64 int) f64)
  (lambda (x guess k) (if (= k 0) guess (newton x (f64* .5 (f64+ guess (f64/ x guess))) (- k 1)))))
(define* floats (subr spin (int) int)
  (lambda (k)
    (+ (f64->int (f64-round (f64* 1e6 (newton 2. 1. k))))
       (+ (if (f64< (f64- 0.1 0.3) -0.2) 1 0) (f64->int (f64-floor (f64-neg 2.5)))))))
(floats 6)
