(define env ((load-module "env.fx")))
(define user ((load-module "user-shown.fx") env))
(extract user::one n)
