; Refused
;;; A proposition may call a logic function of a `bool` result only; one of
;;; an `int` is an integer, in a relation.
(define-type ints (listof int acyclic))
(define len (subr pure (ints) int) (lambda (xs) 0))
(define f (subr pure ((xs ints)) ints (ensures r (len r))) (lambda (xs) xs))
