; Verified
;;; The shorthand and the `ensures` it stands for are one type's: each is
;;; within the other, and a test that proves more fits where one that
;;; proves less is expected, as the prover finds.
(define less (subr pure (int int) (bool (then (< 0 1)) (else (<= 1 0)))) <)
(define spelled (subr pure ((i : int) (n : int)) bool
                  (ensures r (and (implies r (< i n)) (implies (not r) (<= n i)))))
  less)
(define weaker (subr pure ((i : int) (n : int)) bool (ensures r (implies r (<= i n)))) spelled)
(define plain (subr pure (int int) bool) weaker)
(define* use (subr pure ((p : (subr pure (int int) (bool (then (<= 0 1)) (else))))) bool)
  (lambda (p) (p 1 2)))
(use less)
