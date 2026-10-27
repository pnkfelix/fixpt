;; ! `c` has no type `ticket`
;; An abstract type kept but not named cannot be named.
(define-type core-sig (load-moduleof "../module-files/made-core.fx" @heap pure))
(define-type tickets (restrict core-sig issue number))
(define c (the tickets ((proj (load-module "../module-files/made-core.fx") @heap pure))))
(define t (select c ticket) ((with c issue)))
