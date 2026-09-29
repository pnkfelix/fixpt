;;; Recursion a million deep, not in tail position, natively: the native
;;; stack is large enough (it was 8 MB, and overflowed here).
(define* tot (subr spin (int) int) (lambda (n) (if (= n 0) 0 (+ n (tot (- n 1))))))
(tot 1000000)
