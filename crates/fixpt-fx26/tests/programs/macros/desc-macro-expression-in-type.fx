;; ! `ident` makes an expression, not a description
(define-syntax ident (macro (_ expr) expr) (syntax-rules ((_ e) e)))
(define-syntax bad (macro (_ expr) expr) (syntax-rules ((_ e) (the (ident int) e))))
1
