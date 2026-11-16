;; ! is placed twice
(define-syntax double
  (macro (_ expr) expr)
  (syntax-rules
    ((_ e) (+ e e))))
