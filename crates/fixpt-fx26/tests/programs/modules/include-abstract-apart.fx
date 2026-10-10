;; ! argument 1 is a b..t, where a a..t is expected
;; Two modules that include what one procedure makes have abstract types
;; of their own, not one another's, though the procedure's type is one.
(define make
  (subr pure (int) (moduleof (abs t type) (val z t) (val get (subr pure (t) int))))
  (lambda (n)
    (module (define-generative t int)
            (define z t (up-t n))
            (define get (subr pure (t) int) (lambda (c) (down-t c))))))
(define a (module (include (make 1))))
(define b (module (include (make 2))))
(with a (get (with b z)))
