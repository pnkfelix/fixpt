; Integer literals past a fixnum (PLAN.md Q2): each read as arithmetic on
; fixnums, the same in both parsers, so every path gives the same bignum.
(define* big-sum (subr pure () int)
  (lambda ()
    (+ 1152921504606846976 (- 1000000000000000000000 -99999999999999999999999))))
(big-sum)
