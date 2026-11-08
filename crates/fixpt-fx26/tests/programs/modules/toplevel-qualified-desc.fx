;; => 4
;; A description given to `proj`: the top level's `t`.
(define-type t int)
(define id (poly ((a type)) (subr pure (a) a)) (plambda ((a type)) (lambda ((x a)) x)))
(define g (poly ((t type)) (subr (read (globals id)) () int))
  (plambda ((t type)) (lambda () ((proj id #%toplevel:t) 4))))
((proj g bool))
