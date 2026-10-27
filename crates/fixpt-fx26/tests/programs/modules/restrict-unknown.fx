;; ! the module gives no `nope`
(define-type core-sig (load-moduleof "../module-files/made-core.fx" @heap pure))
(define-type tickets (restrict core-sig issue nope))
