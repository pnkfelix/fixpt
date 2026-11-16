;; => (7 6)
;; Members of one signature that bind differently, told apart by shape:
;; `body` in the scope of `x` in the first, nothing bound in the second.
(define-syntax bind (trailmark))
(define-syntax with1
  (macro (letrec-shape ((form (union (bound ((trailmark bind) x @ bvar e @ expr body @ expr)
                                          (bind x in body))
                                   (plain (expr expr)))))
           (_ . form))
         expr)
  (syntax-rules #:trailmarks (bind)
    ((_ bind x e body) (let ((x e)) body))
    ((_ e body) (begin e body))))
(list (with1 bind y 3 (+ y 4)) (with1 5 6))
