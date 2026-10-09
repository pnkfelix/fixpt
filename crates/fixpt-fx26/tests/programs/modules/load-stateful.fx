;; ! a loaded file is one value for all its loads, made once, so making it must be pure
;; Every load of a path is one value, made once, so making it must be pure:
;; a file whose module has state gives a `lambda` making it instead.
(define s (load-module "../module-files/stateful.fx"))
0
