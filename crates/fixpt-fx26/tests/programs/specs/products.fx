; Verified
;;; Products by literals are linear.
(define f (subr pure ((x int)) int (ensures r (= r (* 3 x 2)))) (lambda (x) (* 6 x)))
(f 2)
