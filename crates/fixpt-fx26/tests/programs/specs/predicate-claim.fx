; Refused
;;; `(implies r p)` in an `ensures` is what a test proves where true, as
;;; `(bool (then p) (else))` says it: the checker narrows by it at a branch
;;; on a call, and does not prove it of a `lambda`'s body, so none may claim
;;; it (`predicate.fx` says the same as the verifier's alone).
(define pos? (subr pure ((x int)) bool (ensures r (implies r (< 0 x))))
  (lambda (x) (< 0 x)))
(pos? 3)
