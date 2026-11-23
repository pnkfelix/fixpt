;; ! argument 1 is a b.m2..t, where a b.m1..t is expected
;; A parameter is a path's base too, each call's value one module: its
;; members `m1` and `m2`, of one module type, are two (`TODO.md` §308).
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
(define f (subr pure ((moduleof (val m1 sig) (val m2 sig))) int)
  (lambda (b) (with b ((with m1 value) (with m2 zero)))))
(f both)
