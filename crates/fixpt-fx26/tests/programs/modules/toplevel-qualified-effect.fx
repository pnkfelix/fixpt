;; => 7
;; An effect: the top level's `loud`, not the `plambda`'s effect variable.
(define cell (ref int @heap) (new 7))
(define-effect loud (maxeff (read @heap) (read (globals cell))))
(define g (poly ((loud effect)) (subr #%toplevel:loud () int))
  (plambda ((loud effect))
    (lambda () ((the (subr #%toplevel:loud () int) (lambda () (get cell)))))))
((proj g pure))
