; Rejected: a list that may still be written is not data.
(define f (subr (read @r) ((listof int @r)) int) (lambda (xs) (acyclic xs (ok 1) 0)))
