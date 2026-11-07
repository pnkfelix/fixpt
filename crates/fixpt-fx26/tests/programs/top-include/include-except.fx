;; => 42
;; `(include m (except name …))`: all `m` gives but the names listed.
(define m (load-module "../module-files/include-lib.fx"))
(include m (except both))
(define both int 1)
(+ both (- (value zero) 1))
