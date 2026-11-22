;; ! argument 1 is a e-b.m-base..t, where a e.m-base..t is expected
;; A bundle over another making of the first: its member's values are of that
;; making's type, which this one's procedure does not take.
(define e ((load-module "../module-files/dm-penv.fx")))
(define e-b ((load-module "../module-files/dm-penv.fx")))
(define e2 ((load-module "../module-files/dm-penv2.fx") e-b))
((with (with e m-base) value) (with (with e2 m-frame) start))
