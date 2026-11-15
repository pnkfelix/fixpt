;; ! is placed twice
(define-syntax double
  (-> (expr) expr)
  (syntax-rules
    ((_ e) (+ e e))))
