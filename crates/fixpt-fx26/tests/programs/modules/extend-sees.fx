;; => 1616
;; `(extend e0 e1)`'s `e1` sees `e0`'s bindings (FX-91 §2.3.5): `y` is made
;; of `a`'s `z`. Its own shadow them inside it, and `e0`'s keep their own:
;; `f` is `a`'s, still `a`'s `x` where `b`'s `x` takes its place outside.
(define a (module (define x int 1) (define z int 5)
                  (define f (subr pure () int) (lambda () x))))
(define b (extend a (module (define y int (+ z 1))
                            (define x int 10)
                            (define g (subr pure () int) (lambda () (+ x y))))))
(+ (* 1000 ((with b f))) (+ (* 100 (with b y)) ((with b g))))
