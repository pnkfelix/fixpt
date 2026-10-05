;; ! `up-t` is defined twice in this module
;; A generative type's conversions are names the module defines.
(define m (module (define-generative t int) (define up-t int 3)))
