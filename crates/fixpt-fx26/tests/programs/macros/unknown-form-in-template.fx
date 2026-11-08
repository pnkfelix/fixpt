;; ! the prototype does not know `typecase`'s binding structure: not yet in a template
(define-syntax tc
  (expr)
  ((_ e) (typecase e)))
(tc 1)
