;; => 3
;; A module file of one parameter, a dependent module type, where a chain of
;; parameters each restating those before it was.
(define-type env-t (moduleof (val base (load-moduleof "../module-files/dm-base.fx"))
                             (val user (load-moduleof "../module-files/dm-user.fx" base))))
(define b ((load-module "../module-files/dm-base.fx")))
(define u ((load-module "../module-files/dm-user.fx") b))
(define e env-t (module (define base b) (define user u)))
(define fr ((load-module "../module-files/dm-frame.fx") e))
((with fr three))
