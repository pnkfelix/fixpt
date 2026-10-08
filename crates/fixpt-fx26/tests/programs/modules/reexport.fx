;; => 1
;; `(define x (with m x))` in a module: the `x` in the `with` is `m`'s, so
;; `x` is not made from itself.
(define n (module (define m (module (define x int 1))) (define x (with m x))))
(with n x)
