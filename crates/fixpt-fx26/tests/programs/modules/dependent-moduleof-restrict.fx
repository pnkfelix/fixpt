;; => 2
;; `restrict` dropping a member a kept one names keeps it, unnamed: `z`'s
;; `user` and `show` are over the bundle's own `base` still, so what one gives
;; the other takes (`docs/research/dependent-moduleof.md`, §4.5).
(define-type env-t (moduleof (val base (load-moduleof "../module-files/dm-base.fx"))
                             (val user (load-moduleof "../module-files/dm-user.fx" base))
                             (val show (subr pure ((select base t)) int))))
(define b ((load-module "../module-files/dm-base.fx")))
(define u ((load-module "../module-files/dm-user.fx") b))
(define e env-t (module (define base b) (define user u) (define show (with b value))))
(define z (the (restrict env-t user show) e))
((with z show) ((with (with z user) two)))
