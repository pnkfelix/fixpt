;; ! argument 1 is a int, where a shared-counter.fx..t is expected
;; A load's abstract types are named for its file, whatever binds it.
(define c (load-module "../module-files/shared-counter.fx"))
(define u (load-module "../module-files/shared-twice.fx"))
((with u bump) 0)
