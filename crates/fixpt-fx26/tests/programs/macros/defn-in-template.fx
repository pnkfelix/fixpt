;; ! `define` makes a definition, made at the top level by a macro that makes definitions
(define-syntax bad
  (expr)
  ((_ e) (define y e)))
