;;; A loop: a letrec-bound procedure calling itself in tail position.
(define count (subr pure (int) int)
  (lambda (n)
    (letrec ((loop (subr pure (int int) int)
               (lambda (i acc) (if (= i n) acc (loop (+ i 1) (+ acc i))))))
      (loop 0 0))))
(count 10000000)
