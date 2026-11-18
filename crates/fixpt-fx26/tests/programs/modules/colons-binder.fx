;; ! `m::x` is a path, `module::name`, not a name that may be bound
;; A path names; it binds nothing (TODO.md §296).
(define m (module (define x 1)))
(let ((m::x 2)) 3)
