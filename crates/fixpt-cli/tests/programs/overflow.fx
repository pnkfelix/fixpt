;;; Past a fixnum, `*` and `+` fail on every path, the lowered one too,
;;; until `int` is a bignum (PLAN.md, Q2).
(define* dbl (subr spin (int int) int) (lambda (n acc) (if (= n 0) acc (dbl (- n 1) (* acc 2)))))
(dbl 70 1)
