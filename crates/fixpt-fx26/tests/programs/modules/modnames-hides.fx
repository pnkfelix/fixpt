;; ! unbound variable `y`
;; What a `modnames` leaves out is gone: the module is sealed to `x`.
(define m (module (define x int 1) (define y int 2)))
(define s (modnames x) m)
(with s y)
