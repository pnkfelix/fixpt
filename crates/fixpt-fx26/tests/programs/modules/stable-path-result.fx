;; ! argument 1 is a other.m1..t, where a both.m1..t is expected
;; A procedure's result at its parameter's path, `(select (with $1 m1) t)`,
;; is at the argument's path where it is called: `other`'s, not `both`'s.
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
(define f2 (lambda ((b (moduleof (val m1 sig) (val m2 sig)))) (with b (with m1 zero))))
(define other (module (define m1 (make #f)) (define m2 (make #t))))
((with both (with m1 value)) (f2 other))
