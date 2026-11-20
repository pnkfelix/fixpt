;; => 14
;; A file whose `module-parameters` has strings among its binders, as notes:
;; given two modules, no more (Heist's should-work note, entry 19).
(define m-base (load-module "../module-files/mp-base.fx"))
(define m-noted ((load-module "../module-files/mp-noted.fx") m-base m-base))
((with m-noted both))
