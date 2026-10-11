;; => (9223372036854775808 18446744073709551616 -9223372036854775805 6 42)
;; An `i64` or `u64` is the exact integer it stands for: an `int` where one
;; is wanted (`TODO.md` §63), a bignum past a fixnum, on every machine; in
;; native code, raw in a register, boxed where an `int` is wanted.
(define-type ints (listof int @heap))
(define* up (subr pure (int) int) (lambda (x) (+ x 1)))
(define* wide (subr (alloc @heap) (i64 u64) ints)
  (lambda (a b)
    (list (up a) (up b) (+ (up (i64- 0 a)) 1) (* (i64->int 2) 3) (i64->int (i64+ 40 2)))))
(define* run (subr (alloc @heap) (int) ints)
  (lambda (k) (wide 9223372036854775807 18446744073709551615)))
(run 0)
