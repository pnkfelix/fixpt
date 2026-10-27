; Verified
;;; A specification under a `poly`, instantiated with it.
(define first (poly ((t type))
                (subr pure ((x : int) (y : t)) int (requires (< 0 x)) (ensures r (= r x))))
  (plambda ((t type)) (lambda (x y) x)))
((proj first int) 3 4)
