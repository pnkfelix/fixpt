; Verified
;;; `(- x)` is `(- 0 x)`.
(define f (subr pure ((x : int)) int (ensures r (= r (- x)))) (lambda (x) (- 0 x)))
(f -3)
