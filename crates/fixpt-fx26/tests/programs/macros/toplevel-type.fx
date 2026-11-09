;; => 6
;; A type a template writes is read as the top level reads it,
;; `(select #%toplevel idx)`: the `define-type`'s `int`, not the type
;; variable `idx` the use's `plambda` binds.
(define-type idx int)
(define-syntax as-idx (expr)
  (syntax-rules ()
    ((_ e) (the idx e))))
(define g (poly ((idx type)) (subr pure (idx) int))
  (plambda ((idx type)) (lambda ((x idx)) (+ (as-idx 5) 1))))
((proj g bool) #t)
