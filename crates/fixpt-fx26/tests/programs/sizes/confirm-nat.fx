;;; `confirm-nat`: an integer found no less than 0 is a `nat`, and a
;;; countdown on it needs no `spin`; one found below 0 takes the `else`.
(define* count (subr pure (nat) int) (lambda (n) (if (= n 0) 0 (+ 1 (count (- n 1))))))
(define* safe (subr pure (int) int) (lambda (i) (confirm-nat i (n (count n)) -1)))
(+ (* 10 (safe 7)) (safe -3))
