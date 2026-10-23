; Verified
;;; A convention, then a specification.
(define f (subr (conv fx) pure ((x int)) int (ensures r (= r x))) (lambda (x) x))
(f 1)
