; PLDI '89's C1, `twice`, from its signature: the `lambda`s need no
; parameter types, and no `plambda` is written.
(define twice
  (poly ((t type)) (poly ((e effect)) (subr pure ((subr e (t) t)) (subr (maxeff e spin) (t) t))))
  (lambda (f) (lambda (x) (f (f x)))))

((twice (lambda ((n int)) (+ n 1))) 5)
