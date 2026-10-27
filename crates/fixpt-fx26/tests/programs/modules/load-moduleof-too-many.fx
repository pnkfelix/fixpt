;; ! what `../module-files/made-core.fx` makes is a (moduleof
;; Given more than its parameters, a file's module is given too much.
(define-type core-sig (load-moduleof "../module-files/made-core.fx" @heap pure @heap))
