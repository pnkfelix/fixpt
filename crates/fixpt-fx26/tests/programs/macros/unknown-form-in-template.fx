;; ! the prototype does not know `typecase`'s binding structure: not yet in a template
(define-syntax tc
  (macro (expr) expr)
  (syntax-rules
    ((_ e) (typecase e))))
(tc 1)
