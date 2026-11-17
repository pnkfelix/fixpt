;; ! `(select (with mid b) t)`: `(with mid b)` is no path to a module from a variable bound to one
;; A path's every step a module.
(define mid (module (define b 2)))
(the (select (with mid b) t) 1)
