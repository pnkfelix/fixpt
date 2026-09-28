; Rejected: `y`'s size would be forgotten in the parameter of the returned
; subroutine, which would then take any natural where it relies on `y`'s
; own (docs/research/soundness-findings.md, F8).
(define f (poly ((s size)) (subr pure ((nat s)) (subr pure ((nat s)) (nat 0))))
  (plambda ((s size)) (lambda (a) (lambda (b) (- b a)))))
(define k (let ((y (the nat 5))) (f y)))
