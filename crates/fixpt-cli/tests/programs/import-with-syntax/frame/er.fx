(hide (define a int 1) (define b int 2))
(define-syntax get-a (macro (_) expr)
  (er-macro-transformer (lambda (form rename compare) (rename 'a))))
