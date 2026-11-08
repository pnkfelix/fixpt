;; ! `ident` makes an expression, not a description
(define-syntax ident (expr) ((_ e) e))
(define-syntax bad (expr) ((_ e) (the (ident int) e)))
1
