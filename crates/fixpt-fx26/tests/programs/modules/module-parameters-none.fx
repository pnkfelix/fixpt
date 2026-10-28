;; => 4
;; `(module-parameters ())` (Heist's, 2026-10-28): a maker of none, a
;; `lambda` of no parameters around the module, as `load-module` and
;; `load-moduleof` take any file of parameters.
(define m-a ((load-module "../module-files/mp-none.fx")))
(define m-b ((load-module "../module-files/mp-none-user.fx") m-a))
((with m-b get-n))
