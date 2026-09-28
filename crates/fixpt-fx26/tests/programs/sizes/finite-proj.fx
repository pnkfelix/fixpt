; Rejected: the same, with `finite` given by `proj`.
(define g (poly ((n size)) (subr pure ((nlist int n) (nat n)) nat))
  (plambda ((n size)) (lambda (xs k) (if (null? xs) 0 (- k 1)))))
(define one (nlist int finite) (cons 1 nil))
((proj g acyclic) one 0)
