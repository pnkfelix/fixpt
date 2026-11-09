;; ! `ident` makes an expression, not a description
(define-syntax ident (expr) (syntax-rules () ((_ e) e)))
(define-syntax bad (expr) (syntax-rules () ((_ e) (the (ident int) e))))
1
