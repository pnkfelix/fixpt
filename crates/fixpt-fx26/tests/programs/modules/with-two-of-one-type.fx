;; ! argument 1 is a both.m2..t, where a both.m1..t is expected
;; Two members of one module type, opened by `with`, are two modules
;; (`TODO.md` §308): each member module a `with` binds is at the types
;; `(with both m1)` gives it, its path's from `both`, so `m1`'s procedure
;; is given no value of `m2`'s (a string, here).
(define-type sig (moduleof (abs t type) (val zero t) (val value (subr pure (t) int))))
(define make (subr pure (bool) sig)
  (lambda (b)
    (if b
        (module (define-generative t int #:seal up #:unseal down)
                (define zero t (up 7))
                (define value (subr pure (t) int) (lambda (c) (+ (down c) 1))))
        (module (define-generative t string #:seal up #:unseal down)
                (define zero t (up "seven"))
                (define value (subr pure (t) int) (lambda (c) (string-length (down c))))))))
(define both (module (define m1 (make #t)) (define m2 (make #f))))
(with both ((with m1 value) (with m2 zero)))
