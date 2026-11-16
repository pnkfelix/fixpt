;; => 3
;; `let` by ellipsis: each binding's name in the body's scope, all of them
;; together, as the signature says each element exports.
;; As named: ((bindings ((x bvar) (e expr)) …) (body (in expr x …)))
(define-syntax my-let
  (macro (_ ((x @ bvar e @ expr) ...) body @ expr) expr
    (bind (x ...) in body))
  (syntax-rules
    ((_ ((x e) ...) body) (let ((x e) ...) body))))
(my-let ((a 1) (b 2)) (+ a b))
