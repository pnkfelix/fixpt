;; ! a int is expected here, and this is a string
;; Outside an `allof`, a branch a test rules out is checked as before.
(define f (subr pure (symbol) int) (lambda (t) (if (null? t) "none" 1)))
