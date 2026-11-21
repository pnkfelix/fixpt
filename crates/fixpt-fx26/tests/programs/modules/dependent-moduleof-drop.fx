;; => 4
;; A bundle given where its `base` is left out: what `user` and `show` named of
;; it the type wanted says abstractly, `t`, the module's own as the bundle's
;; were; for a bundle a variable names, and one made where it is given.
(define-type env-t (moduleof (val base (load-moduleof "../module-files/dm-base.fx"))
                             (val user (load-moduleof "../module-files/dm-user.fx" base))
                             (val show (subr pure ((select base t)) int))))
(define-type shown (moduleof (abs t type) (val user (moduleof (val two (subr pure () t))))
                             (val show (subr pure (t) int))))
(define b ((load-module "../module-files/dm-base.fx")))
(define u ((load-module "../module-files/dm-user.fx") b))
(define e env-t (module (define base b) (define user u) (define show (with b value))))
(define z1 (the shown e))
(define z2 (the shown (the env-t (module (define base b) (define user u)
                                           (define show (with b value))))))
(+ ((with z1 show) ((with (with z1 user) two))) ((with z2 show) ((with (with z2 user) two))))
