; Verified
;;; `->` takes a specification as `subr` does.
(define f (-> ((x : int)) int (requires (< 0 x)) (ensures r (< x r))) (lambda (x) (+ x 1)))
(f 3)
