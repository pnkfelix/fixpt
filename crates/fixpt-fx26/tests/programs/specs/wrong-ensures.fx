; Unverified
;;; An `ensures` that does not hold: `x` itself is returned where it is
;;; below 0.
(define abs (subr pure ((x : int)) int (ensures r (<= 0 r)))
  (lambda (x) (if (< x 0) x (- 0 x))))
(abs -5)
