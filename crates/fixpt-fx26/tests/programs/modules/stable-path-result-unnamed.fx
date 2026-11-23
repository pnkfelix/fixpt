;; ! argument 1 is a module the procedure's types depend on: give it by name (bind it with `let` first)
;; A procedure's types depend on its argument's paths only where the
;; argument is a path (1ML's valuable paths): an `if` of two modules is
;; none, so the call is refused.
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
((with both (with m1 value)) (f2 (if #t both other)))
