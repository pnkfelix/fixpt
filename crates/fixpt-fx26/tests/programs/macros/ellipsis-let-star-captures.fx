;; ! `e` is placed in the scope of other bindings than its signature says it is
;; A `let` by ellipsis written as a `let*` is refused: each expression
;; would be in the scope of the names before it, which the signature says
;; it is not, so `(my-let ((x 1) (y x)) y)` would see the first `x`.
(define-syntax my-let
  (((export (bvar expr) (rho (A var))) ...) . (import (expr) (rho (A rib))))
  (syntax-rules ()
    ((_ ((x e) ...) body) (let* ((x e) ...) body))))
(define x 10)
(my-let ((x 1) (y x)) y)
