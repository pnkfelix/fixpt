; Verified
;;; A specified loop that uses a value from outside it, `k`: a
;;; specification speaks of its own procedure's parameters only, so the
;;; loop's says what holds whatever `k` is (each step adds 1 either way).
(define count-past (subr spin ((k int) (n int)) int
                     (requires (<= 0 n))
                     (ensures r (= r (+ n k))))
  (lambda (k n)
    (letrec ((loop (subr spin ((i int) (acc int)) int
                     (requires (<= 0 i))
                     (ensures r (= r (+ acc i))))
               (lambda (i acc)
                 (if (= i 0) acc (loop (- i 1) (+ acc (if (< k 0) 1 (- 2 1))))))))
      (+ k (loop n 0)))))
(count-past 3 4)
