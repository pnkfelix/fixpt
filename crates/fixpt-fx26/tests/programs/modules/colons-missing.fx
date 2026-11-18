;; ! `mid::a` gives no value `y`, which the path `mid::a::y` takes from it alone
;; Each name of a path is of the module before it (TODO.md §296).
(define mid (module (define a (module (define x 1)))))
mid::a::y
