;; A file whose module's items are over its earlier items, `user` over its own
;; `base`: its module's type a dependent one, `(select base t)` in `user`'s
;; (`docs/research/dependent-moduleof.md`, step 3). The chain, said once.
(module-parameters ())
(define base ((load-module "dm-base.fx")))
(define user ((load-module "dm-user.fx") base))
