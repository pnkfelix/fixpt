;; ! unbound variable `both`
;; `(only …)` leaves what it does not list.
(define m (load-module "../module-files/include-lib.fx"))
(include m (only zero value))
(both zero)
