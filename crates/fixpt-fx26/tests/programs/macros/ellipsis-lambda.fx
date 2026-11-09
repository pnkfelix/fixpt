;; => 1
;; A list of binders, repeated, binds each of them: a `lambda`'s parameters.
(define-syntax lam
  (bvar ...)
  (syntax-rules ()
    ((_ x ...) (lambda (x ...) 1))))
(define f (subr pure (int int) int) (lam a b))
(f 5 6)
