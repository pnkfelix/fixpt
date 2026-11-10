;; ! `nope` is not an effect
;; An effect name neither the module opened nor anything outside gives.
(define a (module (define-type n int)))
(with a (the (subr nope () n) (lambda () 1)))
