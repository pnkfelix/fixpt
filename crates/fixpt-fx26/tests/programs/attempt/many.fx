;; => 1000
;; Many attempts, half failing, in a loop: none leaks a task or a group.
(define* step (subr nondet (int) int)
  (lambda (i) (attempt (quotient 2 (remainder i 2)) (lambda ((m string)) 0))))
(define* loop (subr (maxeff nondet spin) (int int) int)
  (lambda (i acc) (if (= i 0) acc (loop (- i 1) (+ acc (quotient (step i) 2))))))
(loop 2000 0)
