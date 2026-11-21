;; ! argument 1 is a e2.base..t, where a e1.base..t is expected
;; Two modules a file makes are two: each one's `user` over its own `base`.
(define e1 ((load-module "../module-files/dm-env.fx")))
(define e2 ((load-module "../module-files/dm-env.fx")))
((with (with e1 base) value) ((with (with e2 user) two)))
