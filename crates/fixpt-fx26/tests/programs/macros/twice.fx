;; ! is placed twice
(define-syntax double
  (macro (expr) expr)
  (syntax-rules
    ((_ e) (+ e e))))
