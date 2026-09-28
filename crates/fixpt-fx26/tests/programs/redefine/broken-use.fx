;;; A redefinition at a type a user cannot take breaks the user; a later
;;; use of it is an error that says why.
(define f (subr pure (int) int) (lambda (x) (+ x 1)))
(define g (subr pure (int) int) (lambda (x) (f x)))
(define f (subr pure (string) int) (lambda (s) (string-length s)))
(g 1)
