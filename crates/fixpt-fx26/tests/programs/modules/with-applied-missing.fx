;; ! `f` is not a description function, nor one a module opened by `with` gives
;; A function applied in a `with` body that neither the module nor the
;; outside gives.
(define m (module (define-type n int)))
(with m (the (f int) 1))
