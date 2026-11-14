;; ! `body` is placed in the scope of other bindings than its signature says it is
;; A member's binding structure checked against its clause: `body` is in
;; `x`'s scope, which the first member does not say.
(define-syntax bind (trailmark))
(define-syntax with1
  (oneof ((trailmark bind) bvar expr expr)
         (expr expr))
  (syntax-rules #:trailmarks (bind)
    ((_ bind x e body) (let ((x e)) body))
    ((_ e body) (begin e body))))
1
