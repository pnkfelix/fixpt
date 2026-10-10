;; => 3
;; In `(with m …)`, a name `m` does not give is what it is outside.
(define-type k int)
(define a (module (define-type n bool)))
(with a (the k 3))
