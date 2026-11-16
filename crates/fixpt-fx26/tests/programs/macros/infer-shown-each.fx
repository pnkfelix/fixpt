;; ! inferred: (macro (_ bvar (many expr) (v @ bvar e @ expr) ...) expr (bind v in e) ...)
;; A refused signature inferred, shown in shapes and facts: each repetition's own scope, a fact
;; under `...`.
(define-syntax m
  (syntax-rules
    ((_ x body (v e) ...) (list body (let ((x 1)) body) (let ((v 1)) e) ...))))
(m y 2 (a 1) (b 2))
