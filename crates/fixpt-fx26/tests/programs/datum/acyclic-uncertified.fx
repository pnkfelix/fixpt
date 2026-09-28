; Rejected: `certify-acyclic` only where `acyclic?` has just said so.
(define f (subr pure ((listof int const)) (listof int acyclic)) (lambda (xs) (certify-acyclic xs)))
