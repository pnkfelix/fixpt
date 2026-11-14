;; ! `t` is defined twice in this module
;; A module's own abstract type and one an `include` takes in, of one name.
(module (define-generative t bool #:seal up-t #:unseal down-t)
        (include (module (define-generative t int #:seal up-t #:unseal down-t)
          (define z t (up-t 5)))))
