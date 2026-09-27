; Rejected: `n` sizes every list inside the argument; at `finite` they need
; not be the same length.
(define firsts (poly ((n size)) (subr pure ((listof (nlist int n) finite)) int))
  (plambda ((n size)) (lambda (xss) 0)))
(define two (nlist int finite) (cons 1 (cons 2 nil)))
(firsts (the (listof (nlist int finite) finite) (cons two nil)))
