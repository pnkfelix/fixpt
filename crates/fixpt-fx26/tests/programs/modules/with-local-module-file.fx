;; => 5
;; Heist's problem B, in a module file: the `f` in the `with` is `m`'s.
(define m (load-module "../module-files/with-local-f.fx"))
((with m f))
