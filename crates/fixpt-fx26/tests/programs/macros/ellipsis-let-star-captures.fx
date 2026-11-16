;; ! `e` is placed in the scope of other bindings than its signature says it is
;; A `let` by ellipsis written as a `let*` is refused: each expression
;; would be in the scope of the names before it, which the signature says
;; it is not, so `(my-let ((x 1) (y x)) y)` would see the first `x`.
(define-syntax my-let
  (macro (_ ((x @ bvar e @ expr) ...) body @ expr) expr
    (bind (x ...) in body))
  (syntax-rules
    ((_ ((x e) ...) body) (let* ((x e) ...) body))))
(define x 10)
(my-let ((x 1) (y x)) y)
