;; The second bundle, over the first: its type depends on its parameter.
(module-parameters ((env (load-moduleof "env.fx"))))
(define m-frame ((load-module "frame.fx") env))
