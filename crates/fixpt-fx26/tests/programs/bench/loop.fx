;;; A loop: a letrec-bound procedure calling itself in tail position.
(define count (subr spin (int) int)
  (lambda (n)
    (letrec ((loop (subr spin (int int) int)
               (lambda (i acc) (if (= i n) acc (loop (+ i 1) (+ acc i))))))
      (loop 0 0))))
(count 10000000)
