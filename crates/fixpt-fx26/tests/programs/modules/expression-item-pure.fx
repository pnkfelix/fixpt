;; ! an expression among a module's items is run for what it does as the module is made, and this one only reads
;; An expression that only reads, among a module's items, does nothing:
;; refused.
(define m-base (load-module "../module-files/mp-base.fx"))
(define p ((load-module "../module-files/mp-pure-item.fx") m-base))
