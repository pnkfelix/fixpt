; Verified
;;; An `if` whose value goes on: each way's value, and what that way
;;; knows, kept at the join, as a case each.
(define above-abs (subr pure ((x : int)) int (ensures r (and (<= 1 r) (<= x (- r 1)))))
  (lambda (x) (+ 1 (if (< x 0) (- 0 x) x))))
(above-abs -3)
