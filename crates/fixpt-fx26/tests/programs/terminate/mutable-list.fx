; Rejected: a list at a region that may be written may be cyclic.
(define f (subr (read @r) ((listof int @r)) int) (lambda (xs) (if (null? xs) 0 (f (cdr xs)))))
