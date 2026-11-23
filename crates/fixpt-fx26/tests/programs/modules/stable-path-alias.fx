;; => 8
;; A path's base and a `let` of it are one value, so their paths are one
;; type (the stable path rule: a variable, then selections of a module's
;; members, which never change): `b2`'s `m1` is `both`'s.
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
(let ((b2 both)) ((with b2 (with m1 value)) (with both (with m1 zero))))
