;; ! is placed twice
(define-syntax double
  (expr)
  ((_ e) (+ e e)))
