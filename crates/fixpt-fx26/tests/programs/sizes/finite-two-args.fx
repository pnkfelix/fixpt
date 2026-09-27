; Rejected: `n` sizes both arguments, so it cannot be `finite`: the list
; has one element, and 0 would pass for its length (docs/research/
; soundness-findings.md, F4).
(define g (poly ((n size)) (subr pure ((nlist int n) (nat n)) nat))
  (plambda ((n size)) (lambda (xs k) (if (null? xs) 0 (- k 1)))))
(define one (nlist int finite) (cons 1 nil))
(g one 0)
