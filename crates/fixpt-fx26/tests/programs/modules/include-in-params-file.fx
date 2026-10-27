;; => 0
;; The same, in a file of parameters, the module included made at them.
(define m ((proj (load-module "../module-files/include-in-params-file.fx") @heap)))
(begin (with m z) 0)
