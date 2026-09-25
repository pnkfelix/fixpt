; A top-level name defined twice: the second `define` shadows the first, so
; `before`, which was defined in between, still sees the first. In Scheme a
; second `define` would assign, and `before` would see the second.
(define x 1)
(define before (subr pure () int) (lambda () x))
(define x 2)
(+ (+ (before) (before)) (+ x x))
