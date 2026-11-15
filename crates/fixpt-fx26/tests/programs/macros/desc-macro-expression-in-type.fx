;; ! `ident` makes an expression, not a description
(define-syntax ident (macro (expr) expr) (syntax-rules ((_ e) e)))
(define-syntax bad (macro (expr) expr) (syntax-rules ((_ e) (the (ident int) e))))
1
