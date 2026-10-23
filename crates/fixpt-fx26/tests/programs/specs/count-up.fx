; Verified
;;; Recursion not in tail position: the call's `ensures`, the procedure's
;;; own, assumed after it (partial correctness: what holds if it returns).
(define count-up (subr (maxeff (read (globals count-up)) spin) ((n int)) int
                   (requires (<= 0 n))
                   (ensures r (= r n)))
  (lambda (n) (if (= n 0) 0 (+ 1 (count-up (- n 1))))))
(count-up 10)
