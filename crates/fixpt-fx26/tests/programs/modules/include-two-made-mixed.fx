;; ! argument 1 is a m2..t, where a m1..t is expected
;; An include of a module of two modules one maker made, each its own
;; (`TODO.md` §308): `m1`'s procedure is given no value of `m2`'s.
(define make
  (lambda ()
    (module
      (define-generative t int #:seal up #:unseal down)
      (define zero t (up 0))
      (define value (subr pure (t) int) (lambda (c) (down c))))))
(define m (module (include (module (define m1 (make)) (define m2 (make))))
                  (define x ((with m1 value) (with m2 zero)))))
(with m x)
