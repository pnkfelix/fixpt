;; => 4
;; A module re-exporting another's values under their own names, and a
;; type of it in its lambdas' types (`module-files/reexports.fx`).
(define r (load-module "../module-files/reexports.fx"))
(define twice (with r twice))
(define bump (with r bump))
(twice (bump 1))
