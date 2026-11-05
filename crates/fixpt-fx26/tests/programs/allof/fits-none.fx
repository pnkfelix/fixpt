;; ! this call fits no member of a (allof (subr pure (int) int) (subr pure (string) int))
(define f (allof (subr pure (int) int) (subr pure (string) int)) (lambda (x) 0))
(f #t)
