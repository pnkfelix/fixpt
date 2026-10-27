;; => 1
;; A module type restricted to the names a client uses (`docs/research/
;; derived-signatures.md`, narrowing): `ticket`, not named, stays unnamed.
(define-type core-sig (load-moduleof "../module-files/made-core.fx" @heap pure))
(define-type tickets (restrict core-sig issue number))
(define first (subr (maxeff (read @heap) (write @heap)) (tickets) int)
  (lambda (c) ((with c number) ((with c issue)))))
(first ((proj (load-module "../module-files/made-core.fx") @heap pure)))
