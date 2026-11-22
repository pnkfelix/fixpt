(define env ((load-module "env.fx")))
(import-with-syntax env::m-lib (only make-thing plus-offset))
(extract (make-thing (product (n (plus-offset 2)))) n)
