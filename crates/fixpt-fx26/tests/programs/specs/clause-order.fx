; Refused
;;; `requires` comes before `ensures`.
(define f (subr pure ((x : int)) int (ensures r (< 0 r)) (requires (< 0 x))) (lambda (x) x))
