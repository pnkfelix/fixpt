;; ! `pair-of-t` is not a type
;; A type declared ahead, before the `include`, cannot name what it gives.
(define-type pairs (listof pair-of-t @heap))
(define m (load-module "../module-files/include-lib.fx"))
(include m)
