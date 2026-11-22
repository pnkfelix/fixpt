;; base.fx and lib.fx's instance over it, made once: what a file takes as
;; one parameter, `(env (load-moduleof "env.fx"))`.
(module-parameters ())
(define m-base (load-module "base.fx"))
(define m-lib ((load-module "lib.fx") m-base))
