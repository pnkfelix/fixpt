; Recursion through a signature, and a loop through `letrec`.
(define sum-to (subr spin (int) int)
  (lambda (n) (if (= n 0) 0 (+ n (sum-to (- n 1))))))
(define count (subr spin (int) int)
  (lambda (n) (letrec ((loop (subr spin (int int) int)
                         (lambda (i acc) (if (= i n) acc (loop (+ i 1) (+ acc 1))))))
                (loop 0 0))))
(cons (sum-to 10) (count 1000))
