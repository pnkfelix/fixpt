(define rules (load-module "rules.fx"))
rules
(define er (load-module "er.fx"))
er
(define plain (load-module "plain.fx"))
plain
(define core ((load-module "core.fx")))
(define param ((load-module "param.fx") core))
param
