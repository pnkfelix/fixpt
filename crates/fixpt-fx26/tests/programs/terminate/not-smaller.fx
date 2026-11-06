; Rejected: the argument is no smaller, just different.
(define-type tree (sumof (leaf int) (node (tupleof tree tree))))
(define f (subr pure (tree tree) int)
  (lambda (t u) (tagcase t (leaf n n) (node (a b) (f u t)))))
