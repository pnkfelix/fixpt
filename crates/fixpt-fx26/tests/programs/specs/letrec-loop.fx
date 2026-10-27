; Verified
;;; A loop inside a procedure, named by `letrec`: its `requires` the
;;; invariant, its `ensures` what the outer procedure returns.
(define double (subr spin ((n : int)) int (requires (<= 0 n)) (ensures r (= r (* 2 n))))
  (lambda (n)
    (letrec ((loop (subr spin ((i : int) (acc : int)) int
                     (requires (<= 0 i))
                     (ensures r (= r (+ acc (* 2 i)))))
               (lambda (i acc) (if (= i 0) acc (loop (- i 1) (+ acc 2))))))
      (loop n 0))))
(double 4)
