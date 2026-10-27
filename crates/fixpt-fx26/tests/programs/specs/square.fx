; Unverified
;;; True, but not linear: `x · x ≥ 0` is beyond Fourier–Motzkin, which
;;; takes the product for an unknown of its own. The VC is left open,
;;; written out for a prover outside, which proves it (`fixpt verify`,
;;; with an SMT solver).
(define square (subr pure ((x : int)) int (ensures r (<= 0 r)))
  (lambda (x) (* x x)))
(square -3)
