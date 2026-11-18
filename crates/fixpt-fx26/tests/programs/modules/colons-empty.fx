;; ! `m::` is not a path: a path is names joined by `::`, `module::name`
(define m (module (define x 1)))
m::
