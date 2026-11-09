;; ! is placed in the scope of other bindings than its signature says it is; `m`'s signature, inferred, is
;; A part placed in two scopes, which no signature says.
(define-syntax m
  (syntax-rules ()
    ((_ x e body) (list (let ((x e)) body) body))))
(m y 1 2)
