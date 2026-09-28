; A top-level name defined twice, at a type its uses can take: the second
; `define` assigns the global, so `before`, which was defined in between,
; sees the second, as in Scheme (and in the REPL). To keep the first, bind
; it: `(define before (let ((x x)) (subr pure () int) …))`.
(define x 1)
(define before (subr pure () int) (lambda () x))
(define x 2)
(+ (+ (before) (before)) (+ x x))
