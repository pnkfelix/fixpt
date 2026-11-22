(define env ((load-module "env.fx")))
(define user ((load-module "user-none.fx") env))
(extract user::one n)
