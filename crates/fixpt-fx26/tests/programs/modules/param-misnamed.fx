;; ! `n` is not a description function: to name a parameter, write `(n : type)`
(define f (subr pure ((n int)) int) (lambda (n) n))
