; Verified
;;; A `nat` is no less than 0, which its type says, and the prover is told.
(define plus (subr pure ((m nat) (n int)) int (ensures r (<= n r)))
  (lambda (m n) (+ m n)))
(plus 3 4)
