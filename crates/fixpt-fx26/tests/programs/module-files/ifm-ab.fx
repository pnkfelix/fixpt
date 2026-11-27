;; The bundle: a.fx and b.fx made once, and the two as one module.
(module-parameters ())
(define m-a ((load-module "ifm-a.fx")))
(define m-b ((load-module "ifm-b.fx") m-a))
(define core (extend m-a m-b))
