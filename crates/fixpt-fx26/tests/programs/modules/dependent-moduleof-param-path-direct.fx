;; => 1
;; The second bundle's member's value, given to the first's procedure.
(define e ((load-module "../module-files/dm-penv.fx")))
(define e2 ((load-module "../module-files/dm-penv2.fx") e))
((with (with e m-base) value) (with (with e2 m-frame) start))
