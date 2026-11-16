;; ! `body` is placed in the scope of other bindings than its signature says it is
;; A `letrena` binds its place as a value too: a part in its body is in the
;; scope of both, which its signature says, `(rho (A place))`.
(define-syntax with-arena
  (macro (_ p @ dvar body @ expr) expr (bind p in body))
  (syntax-rules
    ((_ p body) (letrena p body))))
1
