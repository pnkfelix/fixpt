;; ! a tag or label in a template is a keyword
(define-syntax ok-of
  (expr)
  ((_ e) (sum ok e)))
