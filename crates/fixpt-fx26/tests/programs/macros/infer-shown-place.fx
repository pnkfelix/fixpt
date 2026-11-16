;; ! inferred: (macro (_ p @ place body @ (many expr)) expr (bind p in body))
;; A refused signature inferred, shown in shapes and facts: a place's binder, `place`.
(define-syntax with-arena
  (syntax-rules
    ((_ p body) (list (letrena p body) body))))
(with-arena a 1)
