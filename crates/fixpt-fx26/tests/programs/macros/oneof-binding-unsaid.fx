;; ! `body` is placed in the scope of `x`, but its signature says it is in no scope of the
;; A member's binding structure checked against its clause: `body` is in
;; `x`'s scope, which the first member does not say.
(define-syntax bind (trailmark))
(define-syntax with1
  (macro (_ . (oneof ((trailmark bind) bvar expr expr)
         (expr expr))) expr)
  (syntax-rules #:trailmarks (bind)
    ((_ bind x e body) (let ((x e)) body))
    ((_ e body) (begin e body))))
1
