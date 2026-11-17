;; A module file importing an instance's macros: its values' `include` would
;; be of an item, which a module's `include` is made before.
(define a ((proj (load-module "counter.fx") @globals)))
(import-with-syntax a)
(define two int (tick-twice 1))
