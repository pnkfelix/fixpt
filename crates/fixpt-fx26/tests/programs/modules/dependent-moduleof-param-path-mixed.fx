;; ! argument 2 is a (moduleof (val m-frame (moduleof (val start e-b.m-base..t)
;; A file taking both bundles, the second given over another making of the
;; first than the one given: refused, as its type says the second is over the
;; first given.
(define e ((load-module "../module-files/dm-penv.fx")))
(define e-b ((load-module "../module-files/dm-penv.fx")))
(define e2 ((load-module "../module-files/dm-penv2.fx") e-b))
(define u ((load-module "../module-files/dm-puser.fx") e e2))
(with u v)
