;; => 3
;; An `include` of a module a procedure makes when the program runs: its
;; abstract types the including module's own, as a literal's
;; (`include-abstract.fx`).
(define make
  (subr pure (int) (moduleof (abs t type) (val z t) (val get (subr pure (t) int))))
  (lambda (n)
    (module (define-generative t int)
            (define z t (up-t n))
            (define get (subr pure (t) int) (lambda (c) (down-t c))))))
(define a (module (include (make 1))))
(define b (module (include (make 2))))
(+ (with a (get z)) (with b (get z)))
