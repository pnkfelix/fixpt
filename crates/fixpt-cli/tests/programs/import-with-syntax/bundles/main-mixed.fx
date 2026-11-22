(define env ((load-module "env.fx")))
(define env-b ((load-module "env.fx")))
(define env2 ((load-module "env2.fx") env-b))
(define user ((load-module "user.fx") env env2))
user::v
