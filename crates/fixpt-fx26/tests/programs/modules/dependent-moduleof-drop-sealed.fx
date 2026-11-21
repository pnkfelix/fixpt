;; ! argument 1 is a z..t, where a b..t is expected
;; A bundle's `base` left out, its type abstract: not the `base` it was made of's.
(define-type env-t (moduleof (val base (load-moduleof "../module-files/dm-base.fx"))
                             (val user (load-moduleof "../module-files/dm-user.fx" base))))
(define-type users (moduleof (abs t type) (val user (moduleof (val two (subr pure () t))))))
(define b ((load-module "../module-files/dm-base.fx")))
(define u ((load-module "../module-files/dm-user.fx") b))
(define e env-t (module (define base b) (define user u)))
(define z (the users e))
((with b value) ((with (with z user) two)))
