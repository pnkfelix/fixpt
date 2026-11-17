;; ! argument 1 is a mid.a..t, where a other.a..t is expected
;; Two modules' paths are two types, as two modules' are.
(define make
  (lambda ()
    (module
      (define-generative t int #:seal up #:unseal down)
      (define zero t (up 0))
      (define value (subr pure (t) int) (lambda (c) (down c))))))
(define mid (module (define a (make))))
(define other (module (define a (make))))
((with (with other a) value) (with (with mid a) zero))
