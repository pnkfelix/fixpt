;; ! `nope` is not a type, nor one a module opened by `with` gives
;; A type name neither the module opened nor anything outside gives.
(define a (module (define x int 1)))
(with a (the nope 1))
