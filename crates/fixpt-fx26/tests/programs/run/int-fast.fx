; `modulo`, `quotient`, `*` and `arithmetic-shift` of fixnums, in line in
; register code on every machine that has it, and their edges: signs, a
; result past a fixnum (a bignum, the primitive's), long right shifts.
(define-type ints (listof int @heap))
(define* md (subr pure (int int) int) (lambda (x k) (modulo x k)))
(define* qu (subr pure (int int) int) (lambda (x k) (quotient x k)))
(define* mu (subr pure (int int) int) (lambda (x k) (* x k)))
(define* sh (subr pure (int int) int) (lambda (x k) (arithmetic-shift x k)))
(define big int 1152921504606846975)
(list (md 7 3) (md -7 3) (md 7 -3) (md -7 -3) (md 6 3) (md -6 3) (qu 7 2) (qu -7 2) (qu 7 -2)
      (qu (- 0 (+ big 1)) -1) (mu 3 4) (mu -3 4) (mu big 2) (mu -1 (- 0 (+ big 1)))
      (mu 1073741824 1073741824) (sh 1 3) (sh -5 2) (sh 7 -1) (sh -7 -1) (sh 1 60) (sh 3 70)
      (sh -1 -100) (sh 12345 -100))
