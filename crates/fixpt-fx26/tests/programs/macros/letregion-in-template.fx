;; ! the prototype does not know `letregion`'s binding structure: not yet in a template
(define-syntax lr
  (expr)
  ((_ e) (letregion r e)))
(lr 1)
