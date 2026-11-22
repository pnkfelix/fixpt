;; => (1 1)
;; Two modules made by one maker, each a global's: a path from each is of
;; that path's types, `m1.a..t` and `m2.a..t`, not the other's; `q` keeps
;; `m1.a`'s (the cell verifier's rule for a path's types, `TODO.md` §307).
(define make
  (lambda ()
    (module
      (define-generative t int #:seal up #:unseal down)
      (define zero t (up 0))
      (define inc (subr pure (t) t) (lambda (c) (up (+ (down c) 1))))
      (define value (subr pure (t) int) (lambda (c) (down c))))))
(define m1 (module (define a (make))))
(define m2 (module (define a (make))))
(define q (with m1 a))
(define one (with (with m1 a) (inc zero)))
(define two (with (with m2 a) (inc zero)))
(list ((with q value) one) ((with (with m2 a) value) two))
