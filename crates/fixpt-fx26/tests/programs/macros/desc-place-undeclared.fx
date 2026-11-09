;; ! `body` is placed in the scope of other bindings than its signature says it is
;; A `letrena` binds its place as a value too: a part in its body is in the
;; scope of both, which its signature says, `(rho (A place))`.
(define-syntax with-arena
  (dvar (import expr (rho (A dvar))))
  (syntax-rules ()
    ((_ p body) (letrena p body))))
1
