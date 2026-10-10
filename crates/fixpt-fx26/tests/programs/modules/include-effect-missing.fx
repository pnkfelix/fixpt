;; ! `nope` is not an effect, nor one a module included gives
;; In a module with `include`s, an effect name nothing defines is looked for
;; among the modules included, and said so when it is not there.
(define a (module (define x int 1)))
(define m (module (include a) (define f (subr nope () int) (lambda () 1))))
