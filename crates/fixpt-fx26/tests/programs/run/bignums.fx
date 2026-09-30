;;; `int` is an exact integer, a bignum past a fixnum (PLAN.md, Q2), on
;;; every machine: sums and products that grow past one; `=` and `<` on
;;; bignums made apart; back to fixnums; `quotient` and `modulo`; negative
;;; ones. (The 64-bit types' conversions: `native/raw-64.fx`.)
(define-type ints (listof int @heap))
(define* fact (subr spin (int) int) (lambda (n) (if (= n 0) 1 (* n (fact (- n 1))))))
(define* fib (subr spin (int int int) int)
  (lambda (n a b) (if (= n 0) a (fib (- n 1) b (+ a b)))))
(define* bignums (subr (maxeff (alloc @heap) spin) (int) ints)
  (lambda (k)
    (let ((f30 (fact 30)) (f29 (fact 29)) (big (fib 100 0 1)) (small (+ k 5)))
      (list f30 big (if (= f30 (* f29 30)) 1 0) (if (< f29 f30) 1 0) (if (< f30 f29) 1 0)
            (- (+ big small) big) (quotient f30 f29) (modulo f30 1000000007)
            (quotient (- 0 f30) 7) (modulo (- 0 f30) 1000000007) (quotient f30 (- 0 big))
            (- (- 0 1152921504606846975) 2) (quotient (- (- 0 1152921504606846975) 1) -1)))))
(bignums 0)
