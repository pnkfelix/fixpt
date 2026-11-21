;; => 2
;; A module type whose member's type names an earlier member's types, a
;; dependent module type (`docs/research/dependent-moduleof.md`; Heist's
;; should-work note, entry 11): `user` is over the bundle's own `base`, so
;; what one gives the other takes, each read through the bundle's paths.
(define-type env-t (moduleof (val base (load-moduleof "../module-files/dm-base.fx"))
                             (val user (load-moduleof "../module-files/dm-user.fx" base))))
(define b ((load-module "../module-files/dm-base.fx")))
(define u ((load-module "../module-files/dm-user.fx") b))
(define e env-t (module (define base b) (define user u)))
((with (with e base) value) ((with (with e user) two)))
