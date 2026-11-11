;; => 511
;; A file of module parameters that uses its own macros
;; (`module-files/own-macros-params.fx`): `(g 4)` 5, `(h 10)` 11.
(define b (load-module "../module-files/own-macros-base.fx"))
(define u ((load-module "../module-files/own-macros-params.fx") b))
(import u g h)
(+ (* 100 (g 4)) (h 10))
