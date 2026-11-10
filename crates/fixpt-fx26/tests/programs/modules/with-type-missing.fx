;; ! `nope` is not a type
;; A type name neither the module opened nor anything outside gives.
(define a (module (define x int 1)))
(with a (the nope 1))
