;; => 10
;; A module parameter marked `qualified` (Heist's, 2026-10-28): not
;; included; what the file uses of it is named by `import` or reached by
;; `with`.
(define m-base (load-module "../module-files/mp-base.fx"))
(define m-q ((load-module "../module-files/mp-qualified.fx") m-base))
(+ ((with m-q four)) ((with m-q six)))
