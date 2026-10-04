;; ! `f` is bound as a (=> type type), and the description given is not one
;; `pairof` is of kind `(=> type type region type)`, not `(=> type type)`.
(define g (poly ((f (=> type type))) (subr pure () int))
  (plambda ((f (=> type type))) (lambda () 1)))
(proj g pairof)
