(define env ((load-module "env.fx")))
(define env2 ((load-module "env2.fx") env))
(define user ((load-module "user.fx") env env2))
(+ (* 10 user::v) user::w)
