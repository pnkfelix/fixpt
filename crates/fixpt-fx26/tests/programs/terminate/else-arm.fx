;;; A `tagcase`'s `else` sees the same value: no smaller, so this loops.
(define-type t (sumof (a int) (b int)))
(define f (subr pure (t) int) (lambda (x) (tagcase x (a n n) (else y (f y)))))
