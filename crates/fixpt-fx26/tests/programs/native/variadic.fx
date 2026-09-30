;;; Variadic procedures called natively: the count in a register (x9), the
;;; arguments listed by the callee's `vargs` code; past 8, the eighth a list
;;; of the rest. Global ones, ones made at run time over a value, and `apply`.
(define* total (subr spin ((listof int acyclic)) int)
  (lambda (xs) (if (null? xs) 0 (+ (car xs) (total (cdr xs))))))
(define add-up (vsubr (maxeff spin (read (globals total))) int int) (vlambda xs (total xs)))
(define adder (subr pure (int) (vsubr (maxeff spin (read (globals total))) int int))
  (lambda (k) (vlambda xs (+ k (total xs)))))
(define* sum-of-calls (subr (maxeff spin (read (globals adder add-up total))) (int int) int)
  (lambda (i acc)
    (if (= i 0)
        acc
        (sum-of-calls (- i 1) (+ acc (+ (add-up i 1 2) ((adder i) 1 2 3 4 5 6 7 8 9 10 11)))))))
(define spread (subr (maxeff spin (read (globals adder total))) (int (listof int acyclic)) int)
  (lambda (k xs) (apply (adder k) xs)))
(+ (add-up) (* 10 (add-up 1 2 3)))
(+ (apply (adder 1000) (the (listof int @heap) (list 5 6))) (spread 7 (cons 1 nil)))
(sum-of-calls 2000 0)
