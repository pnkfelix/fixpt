;; ! is placed twice
(define-syntax double
  (expr)
  (syntax-rules ()
    ((_ e) (+ e e))))
