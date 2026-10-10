;; => 42
;; An `include`'s effects are in scope in the module's items, as its types
;; are (`TODO.md` §69): `touches` is `effects`'s, in `get`'s type.
(define effects (module (define-effect touches (read @globals))
                        (define-type n int)))
(define m
  (module
    (include effects)
    (define get (subr touches () n) (lambda () 42))))
((with m get))
