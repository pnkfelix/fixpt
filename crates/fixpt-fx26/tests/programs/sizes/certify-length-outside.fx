; Rejected: `certify-length` only where `length-is?` has just said so.
(define f (subr pure ((listof int const)) (vec int 3)) (lambda (xs) (certify-length xs 3)))
