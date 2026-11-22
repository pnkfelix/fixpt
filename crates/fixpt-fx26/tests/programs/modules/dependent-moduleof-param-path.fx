;; => 2
;; A file over a bundle gives out a value of a member's abstract type, `(select
;; (with $1 m-base) t)`, and a bundle over that bundle holds it: each file's
;; types the argument's member's, by its path (`docs/research/
;; dependent-moduleof.md`, §8).
(define e ((load-module "../module-files/dm-penv.fx")))
(define e2 ((load-module "../module-files/dm-penv2.fx") e))
(define u ((load-module "../module-files/dm-puser.fx") e e2))
(with u v)
