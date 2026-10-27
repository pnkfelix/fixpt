;; => 1
;; A file's module type named by a `define-type`, read in order (not ahead)
;; once its file is loaded, and taken by a procedure of a scheduler.
(define-type core-sig (load-moduleof "../module-files/made-core.fx" @heap pure))
(define first-ticket (subr (maxeff (read @heap) (write @heap)) (core-sig) int)
  (lambda (c) ((with c number) ((with c issue)))))
(first-ticket ((proj (load-module "../module-files/made-core.fx") @heap pure)))
