;; ! `t` is defined twice in this module
;; A module's own abstract type and one an `include` takes in, of one name.
(module (define-generative t bool)
        (include (module (define-generative t int) (define z t (up-t 5)))))
