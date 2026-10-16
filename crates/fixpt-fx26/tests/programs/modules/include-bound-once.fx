;; => 367
;; The names a module's items use of the modules it includes, bound once
;; where it is made, after them (`TODO.md` §69): `g`'s lambdas capture `x`
;; and `double`; `inner` binds its own include's `x`, and the `y` it uses is
;; the outer module's. Where a parameter has an included name (`f`'s `x`),
;; the item keeps its own `with`, which names the included one: today the
;; included `x` wins there (21, not 1020; `TODO.md` §69, to fix).
(define a (module (define x int 1) (define y int 20)
                  (define double (subr pure (int) int) (lambda (n) (* 2 n)))))
(define m
  (module
    (include a)
    (define f (subr pure (int) int) (lambda (x) (+ x y)))
    (define g (subr pure (int) (subr pure (int) int))
      (lambda (k) (lambda (j) (double (+ k (+ j x))))))
    (define inner
      (module (include (module (define x int 300)))
              (define h (subr pure (int) int) (lambda (n) (+ n (+ x y))))))
    (define h2 (subr pure (int) int) (lambda (n) ((with inner h) (double n))))))
(+ ((with m f) 1000) (+ (((with m g) 3) 4) ((with m h2) 5)))
