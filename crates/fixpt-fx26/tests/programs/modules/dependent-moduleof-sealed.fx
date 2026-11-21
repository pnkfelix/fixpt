;; ! argument 1 is a e.base..t, where a b..t is expected
;; A dependent module type seals its members as any module type does: `e`'s
;; `base`'s `t` is `e.base..t`, not the `b` it was made of's.
(define-type env-t (moduleof (val base (load-moduleof "../module-files/dm-base.fx"))
                             (val user (load-moduleof "../module-files/dm-user.fx" base))))
(define b ((load-module "../module-files/dm-base.fx")))
(define u ((load-module "../module-files/dm-user.fx") b))
(define e env-t (module (define base b) (define user u)))
((with b value) ((with (with e user) two)))
