;; ! `body` is placed in the scope of other bindings than its signature says it is
;; One rib is not two levels: a `let*` binds `b` inside `a`'s scope.
(define-syntax with2
  (macro (_ (a @ bvar b @ bvar) body @ expr) expr (bind (a b) in body))
  (syntax-rules ((_ (a b) body) (let* ((a 1) (b 2)) body))))
(with2 (x y) (+ x y))
