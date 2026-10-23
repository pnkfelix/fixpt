; Verified
;;; A predicate's `ensures` about its `bool` result: where `pos?` is true,
;;; `x` is above 0. Written `(or (not r) …)`, it is not what a test proves
;;; for the checker, which would narrow by it unproved (`predicate-claim.fx`);
;;; the verifier proves it of the body, and assumes it after each call.
(define pos? (subr pure ((x int)) bool (ensures r (or (not r) (< 0 x))))
  (lambda (x) (< 0 x)))
(define at-least-one (subr (read (globals pos?)) ((x int)) int (ensures r (<= 1 r)))
  (lambda (x) (if (pos? x) x 1)))
(at-least-one -4)
