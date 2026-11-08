;; ! `t` is not a type
;; The top level's `t`: none, whatever binds `t` where it is written.
(define g (poly ((t type)) (subr pure (t) t))
  (plambda ((t type)) (lambda ((x #%toplevel:t)) x)))
1
