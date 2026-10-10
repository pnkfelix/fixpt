;; => 3
;; An `extend` of modules made where they are extended, not bound to a name:
;; their abstract types are the new module's own (`TODO.md` §69; FX-91's,
;; for `e1`'s), and `e1` sees `e0`'s, as a `with` body does.
(define b (extend (module (define-generative t int)
                          (define zero t (up-t 1))
                          (define value (subr pure (t) int) (lambda (x) (down-t x))))
                  (module (define-generative u int)
                          (define next (subr pure (t) u) (lambda (x) (up-u (+ (value x) 1))))
                          (define get (subr pure (u) int) (lambda (y) (down-u y))))))
(with b (+ (get (next zero)) 1))
