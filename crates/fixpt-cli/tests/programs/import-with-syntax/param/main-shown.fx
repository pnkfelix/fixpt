(define base (load-module "base.fx"))
(define lib ((load-module "lib.fx") base))
(define user ((load-module "user-shown.fx") base lib))
(extract user::one n)
