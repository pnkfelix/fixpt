;; Definitions alone: as a module file `b` is pure, `a` fixed; as a
;; program, `a` a global a later definition may change, so `b` reads it.
(define a int 1)
(define b (subr pure () int) (lambda () a))
