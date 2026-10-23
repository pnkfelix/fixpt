; Verified
;;; A predicate's `ensures` about its `bool` result, as a latent
;;; proposition says it: where `pos?` is true, `x` is above 0.
(define pos? (subr pure ((x int)) bool (ensures r (implies r (< 0 x))))
  (lambda (x) (< 0 x)))
(define at-least-one (subr (read (globals pos?)) ((x int)) int (ensures r (<= 1 r)))
  (lambda (x) (if (pos? x) x 1)))
(at-least-one -4)
