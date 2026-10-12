; Rejected: the returned subroutine relies on its argument being of `a`'s
; length, which is known only where `a` is bound: neither `finite` (F4)
; nor `a`'s own, forgotten (F8), keeps them the same, as for a `nat`.
(define f (poly ((s size))
            (subr pure ((narrayof int s @heap)) (subr pure ((narrayof int s @heap)) (nat s))))
  (plambda ((s size)) (lambda (a) (lambda (b) (array-length b)))))
(define g (subr (read (globals f)) ((arrayof int @heap)) (subr pure ((arrayof int @heap)) nat))
  (lambda (p) (let ((a p)) (f a))))
