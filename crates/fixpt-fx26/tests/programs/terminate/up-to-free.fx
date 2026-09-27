;;; Counting up to a bound fixed for the whole recursion: a variable from
;;; outside the loop.
(define sum-to (subr pure (int) int)
  (lambda (n)
    (letrec ((loop (subr pure (int int) int) (lambda (i acc) (if (< i n) (loop (+ i 1) (+ acc i)) acc))))
      (loop 0 0))))
(sum-to 10)
