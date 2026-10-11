;; ! `f` is bound as a Flat, and the description given is not one
;; A flat binder is given a flat.
(define h (poly ((f flat)) (subr pure () int)) (plambda ((f flat)) (lambda () 1)))
((proj h int))
