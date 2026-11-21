;; ! `z` gives other names than were read from the program before it was checked: its type gives `%hidden:base`, which the program took to be bound outside it
;; A member `restrict` keeps unnamed is named by no client.
(define-type env-t (moduleof (val base (load-moduleof "../module-files/dm-base.fx"))
                             (val user (load-moduleof "../module-files/dm-user.fx" base))))
(define b ((load-module "../module-files/dm-base.fx")))
(define u ((load-module "../module-files/dm-user.fx") b))
(define e env-t (module (define base b) (define user u)))
(define z (the (restrict env-t user) e))
(with z %hidden:base)
