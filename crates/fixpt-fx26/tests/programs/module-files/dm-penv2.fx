;; A second bundle, over the first: its member's types are the first's, so
;; its type depends on its parameter, `(load-moduleof "dm-penv2.fx" env)`.
(module-parameters ((env (load-moduleof "dm-penv.fx"))))
(define m-frame ((load-module "dm-pframe.fx") env))
