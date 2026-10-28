;; ! `c` has no type `ticket`
;; Nor through a parameter whose type keeps an abstract type unnamed
;; (`restrict`): the type is refused where it is read, as a `select` of a
;; module bound there is (`restrict-unnamed.fx`).
(define-type core-sig (load-moduleof "../module-files/made-core.fx" @heap pure))
(define-type tickets (restrict core-sig issue number))
(define g (subr pure ((c : tickets) (select c ticket)) int) (lambda (c t) 0))
0
