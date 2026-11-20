;; A module file by its header, which begins no program.
(module-parameters ())
(define a int 1)
(define b (subr pure () int) (lambda () a))
