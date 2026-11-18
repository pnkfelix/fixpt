;; ! `m` gives no value `y`, which the path `m::y` takes from it alone
;; A path's name is the module's alone, never one bound outside it, as a
;; `with`'s body's may be (TODO.md §296).
(define m (module (define x 1)))
(define y 5)
m::y
