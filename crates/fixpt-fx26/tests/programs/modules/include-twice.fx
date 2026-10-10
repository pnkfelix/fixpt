;; ! `x` is defined twice in this module
;; Two modules included give a name twice: one bucket, no shadowing.
(define a (module (define x int 1)))
(define b (module (define x int 2)))
(module (include a) (include b))
