;; => 15
;; `attempt-within` (Heist's, `TODO.md` §211, 1): a body that ends within
;; its budget gives its value, as `attempt`'s does.
(define* sum-to (subr spin (int int) int)
  (lambda (n acc) (if (= n 0) acc (sum-to (- n 1) (+ acc n)))))
(attempt-within 10000 (sum-to 5 0) (lambda ((m string)) -1) (lambda () -2))
