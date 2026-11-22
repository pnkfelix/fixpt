(define env ((load-module "env.fx")))
(define framed ((load-module "framed.fx") env))
(import-with-syntax framed (only make-thing))
(extract (make-thing (product (n 3))) n)
