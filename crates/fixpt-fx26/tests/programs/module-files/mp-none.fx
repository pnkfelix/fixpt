;; A module of state of its own and no parameters: made once, by whoever
;; loads it, as `((load-module "mp-none.fx"))`.
(module-parameters ())
(define n (ref int @heap) (new 4))
