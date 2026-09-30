;;; Past a fixnum, an `int` is a bignum on every path, the lowered one too
;;; (PLAN.md, Q2): 2^70.
(define* dbl (subr spin (int int) int) (lambda (n acc) (if (= n 0) acc (dbl (- n 1) (* acc 2)))))
(dbl 70 1)
