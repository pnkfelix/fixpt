; Rejected: frozen data that was written while it froze may be cyclic.
(define f (subr pure ((listof int const)) int) (lambda (xs) (if (null? xs) 0 (f (cdr xs)))))
