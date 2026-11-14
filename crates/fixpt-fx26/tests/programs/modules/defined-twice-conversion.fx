;; ! `up-t` is defined twice in this module
;; A generative type's conversions are names the module defines.
(define m (module (define-generative t int #:seal up-t #:unseal down-t) (define up-t int 3)))
