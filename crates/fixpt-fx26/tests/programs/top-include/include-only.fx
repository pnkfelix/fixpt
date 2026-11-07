;; => 42
;; `(include m (only name …))`: of what `m` gives, the names listed, a type
;; among them as a value is, unmarked (`import-with-syntax`'s `only`).
(define m (load-module "../module-files/include-lib.fx"))
(include m (only zero value t))
(define both (subr (alloc @heap) (t) (pairof t t @heap)) (lambda (v) (cons v v)))
(value (car (both zero)))
