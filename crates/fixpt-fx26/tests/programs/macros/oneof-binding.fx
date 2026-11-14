;; => (7 6)
;; Members of one signature that bind differently, told apart by shape:
;; `body` in the scope of `x` in the first, nothing bound in the second.
(define-syntax bind (trailmark))
(define-syntax with1
  (oneof ((trailmark bind) bvar expr (import expr (rho (AD var))))
         (expr expr))
  (syntax-rules #:trailmarks (bind)
    ((_ bind x e body) (let ((x e)) body))
    ((_ e body) (begin e body))))
(list (with1 bind y 3 (+ y 4)) (with1 5 6))
