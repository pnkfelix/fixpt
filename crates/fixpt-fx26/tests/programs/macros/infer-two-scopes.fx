;; ! `m` is refused: no signature is written, and the one inferred from its clauses does not fit them: `body` is placed
;; A part placed in two scopes, which no signature says.
(define-syntax m
  (syntax-rules
    ((_ x e body) (list (let ((x e)) body) body))))
(m y 1 2)
