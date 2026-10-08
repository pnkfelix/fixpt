;; A module's file of parameters that loads another, giving it its own
;; region, and re-exports from it.
(module-parameters ((r region) (unused region)))
(define t ((proj (load-module "tally.fx") r)))
(define tick (with t tick))
(define tick-twice (subr (maxeff (read r) (write r)) () int)
  (lambda () (begin (tick) (tick))))
