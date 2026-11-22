(define env ((load-module "env.fx")))
(define user ((load-module "user-path.fx") env))
(+ (* 100 (extract user::one n)) (extract user::two n))
