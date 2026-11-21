;; ! `e` is declared a env-t: a env-t is expected here
;; A bundle whose `user` is over another `base` than its own does not fit.
(define-type env-t (moduleof (val base (load-moduleof "../module-files/dm-base.fx"))
                             (val user (load-moduleof "../module-files/dm-user.fx" base))))
(define b ((load-module "../module-files/dm-base.fx")))
(define b2 ((load-module "../module-files/dm-base.fx")))
(define u2 ((load-module "../module-files/dm-user.fx") b2))
(define e env-t (module (define base b) (define user u2)))
1
